#include <string.h>
#ifdef _OS_WINDOWS_
#include <malloc.h>
#include <stdalign.h>
#endif
#include "julia.h"
#include "julia_internal.h"
#include "julia_assert.h"
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// To disable debug printing
//#define st_fprintf(...) fprintf(__VA_ARGS__)
#define st_fprintf(...)
//#define jl_(...)

size_t indent = 0;
void print_indent( void ) {
    st_fprintf(stderr, "%*s", indent, "");
}

/**
 *
 * TODO: The reality of the matter is that 99.99% of tuple
 * checks are going to be handled correctly based on:
 *   (1) volume check
 *   (2) separable coverage check (no gaps)
 *        -> Both handled at top-level, when exiting tuple
 *   (3) total coverage check (best alternative)
 *        -> I think the idea here is that we make sure all the
 *           mask bits are covered by some alternative
 *           that has non-zero area...
 *        -> Can't quite remember though. Might be worth
 *           some brainstorming.
 *   (4) zero-volume pruning
 *        (any empty component is just an overall FAIL)
 *        -> Both handled eagerly, by tuple aggregator
 *
 *   My code should try to handle these correctly, rather
 *   than dedicating a tone of extra effort to efficiently
 *   solving the case where all 4 of these are wrong.
 *     -> Accept your fate, Cody.
 *
 *  REWRITE this code to be simpler, accepting this.
 *   
 **/

/**
 * Here's the dependency plan:
 *
 * The challenge is that we need to consider the possibility that
 *   Tuple{U{ ... }, U{ ... }, ... } <: U{Tuple{ ... }, Tuple{ ... }}
 *
 * Which means when checking that direction we group all of the appropriately-
 * sized tuples together and feed them into a "hyper-cube" algo.
 *
 * This algorithm needs to take a (<:) Union-Union measurement against the 
 * components of each of the tuples on the RHS.
 *   - Each LHS component is either not covered, covered, or covered conditionally
 *
 * So we have a bit-vector representing our "cubic-AND"
 *   (i.e. we need to check that the volume is filled based on this sampling)
 *
 * This could be done:
 *   a. eagerly - we measure the tuple in all components, and then immediately
 *      descend into 2^N hyper-cube comparison (exponentially many *repeated, masked*
 *      versions of the original problem)
 *   b. lazily - sample all of the tuples against the LHS, and use some size/volume/
 *      quantity heuristics for early exit. Main difference is that we can start with
 *      the tuple that covers the most dimensions (ideally unconditionally) and if
 *      no dimension is covered completely we give up, etc.
 *
 *      - It's exactly equivalent to checking that our 2^N hypercube is covered
 *        by the OR of RHS options.
 *
 *  I'm inclined to say that (b) is the right way to solve the problem, since it's
 *  conspicuously efficient. (a) seems like to spend a lot of effort recursing into
 *  partial coverage scenarios when in reality we have no chance to cover. It's also
 *  very slow for the case that distribution does happen.
 *
 *  Okay, that's enough to convince me to do a two-phase, "sample & solve" approach.
 *
 *  It's exactly as we had it before, except that we propagate proof obligations.
 **/

/**
 * What about the UnionAll/Union Distributivity?
 *
 *   -> Is there a similar hyper-cube problem I can cast my situation onto?
 *   -> Or is it best to think of this as lifting the unioning to the tuple level,
 *      and matching to "copied"/"repeated" UnionAlls?
 *
 * I suspect that both of these interpretations are valid, and are likely
 * the same thing.
 *
 * Union{Tuple{ ... }, Tuple { ... }} where T
 *
 * Tuple{x where T, y where U}
 * Tuple{x, y} where {T, U} <- Cartesian product is already built-in here
 *
 * Tuple{Union{Ref{X},Ref{Y}}, ... } <: Tuple{Ref{T}, ... } where T
 *    <- The biggest deviation from our other problem is that
 *       the ways UnionAlls can vary is more complicated
 *
 * We don't want to expand up by lifting Unions because that is exponential too:
 *   Tuple{Union{Ref{X},Ref{Y}}, ... } -> Union{Tuple{Ref{X}, ...}, Tuple{Ref{Y}, ...}, ...}
 *
 * What I want to do is lower the matching rules "into the hyper-cube"
 *   -> I can union anything in the tuple as long as they are independently
 *      compatible with the UnionAll
 *
 *      -> So when do I know that "corners" happen (i.e. things vary incompatibly)?
 *
 *      -> Canonical example would be:
 *      Tuple{Union{Ref{Int}, Ref{Bool}}, Union{Ref{Int},Ref{Bool}}, ... } </: Tuple{Ref{T}, Ref{T}, ...} where T
 *
 *           -> This is the awkward position we end up in.
 *           -> We have to know that each solution generated in one part of the tuple is valid
 *              in Cartesian product with ever other solution generated.
 *
 *              -> If I had saved my bounds from the Union, I'd check that their O(N^2) combinations are compatible
 *                 Which is unfortunately exponential, but I suspect there may not be a lot to reduce that.
 *
 *                 For example, I can match T against a lot of `Union` that give loose but informative bounds.
 *                 Then, I'm allowed 
 *
 *
 *                  Union{Int,Bool,String,Float64}  <: Union{Int,Bool,String,T} 
 *                  Union{Int,Bool,String,Float32}  <: Union{Int,Bool,String,T} 
 *
 *                  -> Float64 <: T <: Union{... }
 *                  -> Float32 <: T <: Union{... }
 *                  
 *                  In another component:
 *                  Ref{Union{String, Float32}} <: Ref{Union{Float32, Float64, T}}
 *                  Ref{Union{String, Float64}} <: Ref{Union{Float32, Float64, T}}
 *
 *
 *  Indeed:
 *     Tuple{Union{Ref{Union{Float64, Float32, Bool}},  Ref{Union{Float64, Float32, Int}}},
 *           Union{Ref{Union{Int,Bool,String,Float64}}, Ref{Union{Int,Bool,String,Float32}}}}
 *      <: (Tuple{Ref{Union{Float32,Float64,T}}, Ref{Union{Int,Bool,String,T}}} where T)
 *
 *  Why? Because all of the bounds in the first component are compatible with all the bounds
 *  in the second component.
 *    -> Another "exponential check" for an initially fast sampling. The unfortunate part
 *       is that our checks here are much more expensive than the bit-checks for distributing
 *       over tuples.
 *    -> This is exactly equivalent to allowing 2^N UnionAlls to be evaluated, except
 *       that we can compute their bounds as combinations of bounds from each component.
 *
 *  Cool! We have an algorithm.
 *
 *     Just one TODO: What are the conditions to allow this? Is it all Unions within a tuple
 *     or is there something special? Do we need to think about the "covariant region" of a
 *     UnionAll var, and how do we handle bounds generated on other vars if so?
 *
 * Side-note: I *think* this problem is one-directional, since distributivity can only happen
 *            in the covariant region of the UnionAll.
 *
 *    TODO: Write out the opposite direction case and see if there's any way to distribute.
 *
 *      Tuple{F(T) where T, F(U) where U} <: Union{Tuple{ ... }}
 *        -> Ah, this is true. F(T) where T might only be covered by multiple RHS tuples.
 *           but is this the distributivity algorithm we already designed above? I think it is...
 *
 *  In *FACT* I need to think carefully about the proof obligations.
 *     -> It's important that I allow a "point" with a proof obligation to be covered by a point
 *        without one, but only if it means we might remove that obligation entirely. (complicates the solver)
 *
 *  So these are starting to look like two sides of the same coin.
 *
 *       <-- TODO list exact action matrix here -->
 *
 *
 *  Every bit in the hyper-cubes we are checking coverage for requires a "compatible bounds check."
 *    -> This suggests that our proof obligation tree might actually *explode*
 *  
 *  Which means... maybe we need to move this *whole* thing to the solve phase?
 *    -> Expanding the proof obligation tree early sounds like a nightmare.
 *
 *    -> Yes, this is the right solution. Just have to think about how to encode
 *       the hyper-cube options...
 *
 *    -> Wow, so we measure all the components only (maybe fail early) and then solve at the end!
 *       The distributivity problem ended up re-using our tree after all!
 *
 *        -> Only early-exit criterion is a basic volume check
 **/

 /**
  * What do we want to store from a hyper-cube?
  *   - It looks kind of like an AND/OR except that we are checking total coverage
  *     and we sometimes have null-proof terms
  *
  * This is enough "interesting data" that it's time to abandon
  * the GC and allocate everything directly.
  *
  * For efficiency, we definitely want to support:
  *   - Entirely evidence-free hyper-cubes
  *   - hyper-cubes with independent evidence in a few different dimensions
  *   - etc.
  *
  * So most likely we want:
  *   - evidence-free + evidence-required bitmasks
  *   - volume per-sample ?
  *     -> Nah, the volumes are dynamic anyway
  * 
  * So let's figure out how we want to do this allocation...
  *   1. I need a way to identify the object type, now that
  *      it won't include the object bits
  *   2. I want to binarize the AND node so that it is efficient
  *      to merge
  *   3. We will use pointers for now and can switch to indices
  *      later
  *   4. I need some kind of "union-hyper-cube" data structure
  *
  * I will probably treat these as an efficiently-allocated sum type.
  *   -> Padding is unfortunate
  *
  *   -> Can also store the type with the pointer
  *
  **/

typedef struct jl_stbound_t {
    struct jl_stbound_t *prev;
    enum { UPPER, LOWER } kind;
    jl_value_t *bound;
} jl_stbound_t;


//typedef struct {
//} jl_union_hypercube_t;


// This list fills me with determination.

/**
 * List of types:
 *  [x] Any
 *  [x] Union
 *      [x] Union{ }
 *      [x] Union{ ... }
 *  [x] Kinds
 *      [x] typeof(Union{ })
 *      [x] typeof(Union{...})
 *      [x] UnionAll
 *      [x] DataType
 *  [~] Tuples
 *      [x] No inside unions
 *      [ ] Distributivity with Unions
 *  [x] DataTypes
 *      [x] Primitive types
 *      [x] 0-parameter DataTypes
 *      [x] N-parameter DataTypes
 *
 * Other features:
 *  [~] TypeVars
 *      [ ] Statically diagonal
 *      [~] Statically non-diagonal
 *          [x] For-all
 *          [ ] Existential
 *      [ ] Dynamically diagonal
 *  [ ] Type{T} ?
 *
 **/

/**
 * Our handling of typevars looks like this:
 *   1. Add them to our environment
 **/

// TODO: Later, we'll get the environment back out...


/**
 * TODO:
 *   Might be worth analyzing ahead of time whether variables appear in the right places
 *   to establish constraints.
 *
 *   Variables that *only* appear in covariant positions
 *   never have any constraints to propagate.
 *
 *     -> Unfortunately, we don't know that until *after* (just like being used once)
 *
 *     -> Of course, the diagonal rule means that these *do* end up having constraints, after all!
 *
 *   -> Probably best just to make it very efficient to pop these from our tree
 **/

typedef enum {
    RIGID,
    FLEXIBLE,
} jl_varkind_t;

typedef struct {
    char *buffer;
    size_t sz;
    size_t capacity;
} jl_linear_alloc_t;

/**
 * TODO: I think I need to record the inv_depth 
 *       from wherever I got my bound
 *
 * Thinking about:
 *   Tuple{Ref{T}, T} where T
 *   
 *   -> T should be considered covariant in one of these
 *      positions
 *
 * *OR* is it actually the flexibility I care about?
 *
 * Let's write out the examples and convince ourselves
 * how to track correctly.
 *
 **/

typedef struct jl_varbinding_t {
    jl_tvar_t *var;
    uint16_t id; // TODO: replace var?
    //jl_value_t *lb;
    //jl_value_t *ub;
    jl_varkind_t kind; // \forall vs. exists
    int16_t inv_depth;

    // TODO: innervars?
    struct jl_varbinding_t *prev;
} jl_varbinding_t;

/**
 * TODO: Delete/replace
 **/
typedef struct {
    JL_DATA_TYPE
    uint16_t id;
    uint8_t is_upper;
    jl_value_t *bound;
    jl_varbinding_t *vars;
} jl_tvar_bound_t;

/**
 * TODO: I'd like to think carefully about how I'd solve this problem
 *       without multiple occurrences of RHS variables.
 *
 *  In that case, we only ever have to compare against
 *  "pre-existing" bounds.
 **/

typedef struct {
    int16_t inv_depth;
    uint16_t var_cnt;

    jl_linear_alloc_t *alloc;
} jl_stenv_t;

/**
 * TODO:
 *   1. Add obligation encoding (ugly)
 *   2. Add solver
 *   3. Add variable constraints, etc.
 *   4. Test 
 **/

/**
 * Layout:
 *   (1) Compute maximum bit size up-front and use that to size
 *       all of our bit-vectors.
 *
 *       We'll then have simply
 *
 *       int16_t bvec_sz;
 *       int16_t n_alts;
 *       int16_t n_dims;
 *       int16_t *dims;               // dims[n_dims]
 *       uint64_t *subtype;           // subtype[n_alts][n_dims][bvec_sz]
 *       uint64_t *indeterminate;     // indeterminate[n_alts][n_dims][bvec_sz]
 *       jl_value_t *evidence_chain;  // evidence_chain[n_alts][n_dims]
 **/

struct jl_stsample_t;

typedef struct jl_stobligation2_t {
    struct jl_stsample_t *lhs;
    struct jl_stsample_t *rhs;
    struct jl_stobligation2_t *next;
} jl_stobligation2_t;

typedef struct jl_stsample_t {
    uint16_t subtree_sz;
    uint16_t bvec_sz;
    uint16_t n_alts;
    uint16_t n_dims;

    uint16_t *dims;                     // dims[n_dims]   TODO: Remove
    uint64_t *subtype;                  // subtype[n_alts][n_dims][bvec_sz]
    uint64_t *indeterminate;            // indeterminate[n_alts][n_dims][bvec_sz]
    struct jl_stsample_t **subtrees;    // subtrees[n_alts][n_dims][subtree_sz]
    jl_stobligation2_t **obligations;   // obligations[n_alts][n_dims]
} jl_stsample_t;

// TODO: Replace explicit enum types or switch to C++ (lol)
// TODO: We can allocate in words, for simplicity (and even use 32-bit indices instead?)

typedef struct jl_small_result_t jl_small_result_t;
typedef struct jl_agg_result_t jl_agg_result_t;
typedef struct jl_bound_t jl_bound_t;

enum small_result_type {
    _FALSE = 0, _TRUE = 1,
    _INDETERMINATE_AGGREGATE = 2,
    _INDETERMINATE_BOUND = 3,
};

// Here's the new result:
struct jl_small_result_t { uintptr_t bits; };

// And then the AND/OR structure:
struct jl_agg_result_t {
    uint32_t size;
    enum : uint8_t { AND, OR } type;
    uint8_t is_distributive_tuple : 1;
    uint8_t is_distributive_tuple_root : 1;
    jl_small_result_t results[0];
};

// TODO: Try to improve our flag situation.
//       Maybe even replace with a top-level wrapper or two.
//
        // The tuple root flag is because AND/OR eagerly reduce
        // The tuple contents flag is because non-distributive components eagerly reduce
        // The tuple root flag would be because tuples eagerly collapse their dimensions
        //    (and we might need another for the middle AND)

// And the bounds:
struct jl_bound_t {
    uint32_t var_id;
    enum : bool { SUB, SUPER } type;
    jl_varbinding_t *env;
    jl_value_t *bound;
}; // Pretty much identical to before

static inline bool is_true(jl_small_result_t r) { return (r.bits & 0x3) == _TRUE; }
static inline bool is_false(jl_small_result_t r) { return (r.bits & 0x3) == _FALSE; }
static inline bool is_bound(jl_small_result_t r) { return (r.bits & 0x3) == _INDETERMINATE_BOUND; }
static inline bool is_aggregate(jl_small_result_t r) { return (r.bits & 0x3) == _INDETERMINATE_AGGREGATE; }
static inline bool is_determinate(jl_small_result_t r) { return !(r.bits & 0x2); }

static inline jl_agg_result_t *unwrap_aggregate(jl_small_result_t r)
{
    if ((r.bits & 0x3) != _INDETERMINATE_AGGREGATE)
        return NULL;

    return (jl_agg_result_t *)(r.bits & ~(uintptr_t)0x3);
}

static inline jl_bound_t *unwrap_bound(jl_small_result_t r)
{
    if ((r.bits & 0x3) != _INDETERMINATE_BOUND)
        return NULL;

    return (jl_bound_t *)(r.bits & ~(uintptr_t)0x3);
}

static inline bool unwrap_boolean_unsafe(jl_small_result_t r, size_t *sz)
{
    assert(is_determinate(r));
    if (sz != NULL) *sz = (r.bits >> 2);
    return r.bits & 0x1;
}

static inline jl_small_result_t wrap_boolean_result(bool b, uintptr_t size)
{
    jl_small_result_t result = { .bits = b ? _TRUE : _FALSE };
    result.bits |= size << 2;
    return result;
}

static inline jl_small_result_t wrap_aggregate_result(jl_agg_result_t *agg)
{
    jl_small_result_t result = { .bits = _INDETERMINATE_AGGREGATE };
    result.bits |= (uintptr_t)agg;
    return result;
}

static inline jl_small_result_t wrap_bound_result(jl_bound_t *bound)
{
    jl_small_result_t result = { .bits = _INDETERMINATE_BOUND };
    result.bits |= (uintptr_t)bound;
    return result;
}

/**
 * Nice! Type-safe wrappers around our small result types!
 **/


/**
 * "Simple" tuples are a *major* loss in this scheme, since they now need 64 times the amount of storage for single bits.
 * But I *think* this is the right way to do things anyway. More homogeneous.
 **/

// All aligned at 8-byte boundary, as expected

//char (*__kaboom1)[sizeof(jl_small_result_t)][sizeof(jl_agg_result_t)][sizeof(jl_bound_t)] = -1;
//char (*__kaboom2)[alignof(jl_small_result_t)][alignof(jl_agg_result_t)][alignof(jl_bound_t)] = -1;
// - just making sure the sizes are good

typedef struct {
    int16_t inv_depth;
    uint16_t var_cnt;
    jl_linear_alloc_t *alloc;
} jl_stenv2_t;

enum maybe_bool {
    FALSE = 0,
    TRUE = 1,
    INDETERMINATE = 2,
};

typedef struct {
    jl_value_t *required;
    jl_value_t *choice_tree;
} jl_stobligation_t;

typedef struct {
    enum maybe_bool result;
    jl_stobligation_t condition;
} jl_stresult_t;

typedef struct {
    jl_varbinding_t *vars;
    jl_varkind_t kind; // TODO: default_kind
} jl_varenv_t;


JL_DLLEXPORT jl_stresult_t jl_simple_subtype_env(jl_value_t *x, jl_value_t *y, jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv_t *env);


    /**
     *
     *  With an invariant, all alternatives are effectively isolated
     *    -> Which means that our bit-mask must be complete
     *    -> Which means that we *must* combine all RHS bounds
     *    -> So it is an AND, but it's a lazy AND
     *    -> Do we just resolve it early into a chain?
     *        -> Absolutely we can
     *
     *    -> Inv{Union{ ... }, ... } <: Union{Inv{Union{ ... }, ... }
     *        -> ((bi-directional union) AND (bi-directional union) AND ...)  OR (alternative 2...)
     *           This is an OR-AND-"equals" structure
     *
     *    -> So what we really want to do is reduce this to N alternatives, each of which is a "merged bounds-chain"
     *        -> We knew we wanted to delete the bitmask structure in this case anyway, and now we see why.
     *           There's only a single bit inhabited if we reduce eagerly.
     *
     *    -> Let's do a vectorized OR, since that should re-use more code
     *
     *    -> OR-DEFERRED-AND + distributivity
     *
     *        -> Does this work for double-nesting?
     *           Tuple{Tuple{Union{Int,Bool}}} <: Union{Tuple{Tuple{Int}},Tuple{Tuple{Bool}}}
     *           Tuple{Tuple{Union{Int,Bool}, String}, Bool} <: Union{Tuple{Tuple{Int, String},Bool},Tuple{Tuple{Bool, String},Bool}}
     *            -> TODO: Add test
     *
     *            -> We handle this as a chain of tuple matches (as usual) and the
     *               solver handles those chains specially.
     *                 TODO: Check that we *only* encounter this chain in this circumstance
     *
                 * Example:
                 *   Pair{Tuple{ ... }, Int} <: Pair{Tuple{Ref{T}, T}, U} where T <: U
                 *
                 *    -> So now, when I match against T and check its
                 *       upper bound, I end up inheriting an obligation
                 *       to compare against Int as well.
                 *
                 * TODO:
                 *   Turn into subtype test (or verify coverage)
     *
     *  With the standard one, I have a single type that might be covered
     *  by a union of top-level tuples. In this case, the story is the same
     *  but the "union" on the RHS is a UnionAll
     *
     *    Tuple{Union{Ref{X},Ref{Y}}, ... } <: Tuple{Ref{T}, ... } where T
     *
     **/

/**
 * Same as `jl_count_union_components` except that
 * it also unwraps unionall.
 *
 * TODO: rename
 **/
JL_DLLEXPORT size_t jl_count_nontuples(jl_value_t *v) {
    v = jl_unwrap_unionall(v);
    if (jl_is_uniontype(v)) { 
        jl_uniontype_t *uv = (jl_uniontype_t *)v;
        return jl_count_nontuples(uv->a) + jl_count_nontuples(uv->b);
    } else if (jl_is_datatype(v) && jl_is_tuple_type(v)) {
        return 0;
    } else {
        return 1;
    }
}

JL_DLLEXPORT size_t jl_count_tuples(jl_value_t *v) {
    v = jl_unwrap_unionall(v);
    if (jl_is_uniontype(v)) { 
        jl_uniontype_t *uv = (jl_uniontype_t *)v;
        return jl_count_tuples(uv->a) + jl_count_tuples(uv->b);
    } else if (jl_is_datatype(v) && jl_is_tuple_type(v)) {
        return 1;
    } else {
        return 0;
    }
}


/**
 * This is for matching a tuple/invariant datatype against a general RHS (which may be union/unionall-wrapped)
 *
 *  Proposal:
 *       -> Linked list for bounds-chains
 *       -> Degenerate tuple for top-level unions (and Invariants)
 *           -> Just a "vectorized" OR of bounds-chains
 *
 *  Special cases:
 *       -> Invariant constructors create a "vectorized" OR of bounds-chains (no bitmasks at all)
 *       -> Complete coverage (w/o obligations) by any alternative is an early TRUE
 *       -> Insufficient coverage (by volume, w/ obligations) by all alternatives is an early FALSE
 *       -> If no LHS inner unions, collapse like invariant (nothing to distribute)
 *       -> If no RHS outer unions, collapse like invariant (nothing to distribute)
 *
 *  One interesting note:
 *       -> It can be profitable to delay AND-merging (since that is N^2) until we know that all of
 *          the components can be covered (ignoring conditions)
 *       -> Of course, there are examples in the opposite direction too. I'm not sure which is better.
 *       -> TODO: Make a note and save for benchmarking
 *
 * Supporting re-allocs: One *big* TODO is that we need to handle "tearing"
 *   -> Either we support reallocing and moving this whole thing
 *   -> OR, we always read it as a stream
 **/

jl_varbinding_t *lookup(jl_varbinding_t *vars, jl_tvar_t *tv) {
    jl_varbinding_t *vb = vars;
    while (vb != NULL) {
        if (vb->var == tv)
            break;
        vb = vb->prev;
    }
    return vb;
}

static inline size_t align_forward(size_t addr, size_t align) {
    return (addr + (align - 1)) & ~(align - 1);
}

/**
 * So, I got the inductive part wrong (sort of)
 *   -> The major problem is that we can complete a "cube" arbitrarily deep
 *      from the top level. But the way I was planning on doing this, you'd
 *      have to "stitch together the cubes again after the fact
 *
 *      -> What we *actually* need is the ability to replace individual "pixels"
 *         with their inductive split
 *         TODO: Think about how to allocate these.
 *
 *         -> One thing that would definitely work would be to allocate these
 *            separately (i.e. "true", "indeterminate", "cubic")
 *             -> The key thing is to have all the RHS alternatives contribute
 *                to the same "cubic set"
 *
 *             -> Since this is a function of the LHS types, we can also
 *                preallocate all of the bit-sets sequentially
 *
 *                 -> In this case, instead of allocating a pixel, we allocate
 *                    an entire bitset? That might work...
 *
 *                      -> It does need to *function* like its old pixel though
 *                         (i.e. it contributes to higher-level cubes)
 *
 *  This definitely feels like the right continuation of our theory, at least.
 *
 *  Okay, here's my idea:
 *    - Flags at the top to indicate whether there is any evidence preset and
 *      any higher-level unions (almost always false).
 *    - Higher-order unions are stored as a bit-set + pointers to the higher-
 *      order cube just like our evidence propagation is stored.
 *
 *  Overall, it is very much like typical evidence except that it's not so
 *  alternative-specific. Is there a better indexing that can recover this
 *  inductive structure?
 *
 *    -> For one pixel, I still sample across the RHS alternatives as usual.
 *       With the caveat that:
 *         (1) New alternatives can appear:
 *                  Union{
 *                      Tuple{..., ..., ...} <- Suddenly, we are breaking down these unions
 *                  Union{Tuple{Union{Tuple{Int, Bool}, Tuple{Bool, Bool}}, Int}, ... }
 *                    -> One alternative got mapped to two more
 *
 *         (2) Each alternative needs to be considered as a separate "cubic bit-sample"
 *
 *    -> So we must re-index the # of alternatives
 *    -> The # of LHS components is totally un-related to before
 *    -> And so it the # of components
 *
 *         -> It's an entirely new cube. What makes it harder is that
 *            we don't iterate other RHS alternatives in the inner loop,
 *            so it's hard to predict how many alternatives there will be
 *            up-front. (i.e. I can't "seal" it)
 *
 *    -> Okay, so we're providing a new "grid"
 *         -> Technically the solver _could_ identify this special evidence and
 *            (a) correlate it across (redundant) entries, or (b) expect it to be
 *            allocated once
 *
 *  These options are worth thinking about.
 *    (a) means that we can potentially think about this more as a general "deferral"
 *        -> the RHS is going to naturally measure against the LHS tuple basis (deferring AND-ing)
 *           and then that cubic set is deferred upward yet again
 *  
 *  Of course, the concept is separate from the way it's stored really. No matter
 *  what I'll have to look up all the bit-masks (and evidence) for all the samples
 *  in the solver.
 *     -> And that is all LHS-determined so it's consistent structure
 *
 *  Maybe we should focus less on bit-packing. How would I do this in Julia?
 *     -> Basically the same TBH. Only thing I might switch up is how to look-up
 *        the higher-order cube.
 *
 *     -> Wait. the higher-order behavior is associated with the *LHS*
 *     -> We can either add a list of (comp_i, rhs_alt_i, bit_index) (i,j,k)
 *        OR we can add a bitmask and a list of entries 
 *          -> This can actually be developed as part of our initial scan
 *
 *     -> So at the beginning we scan through all unions & tuples and get
 *        the "tree-basis" that we are forced to sample on.
 *          -> If it weren't for the different # of alternatives, we could
 *             almost just allocate extra bits for the basis
 *
 *     -> Okay, so we lay out these trees contiguously following the first one.
 *         -> Now, can we make the construction order follow a stack-discipline?
 *            -> Not easily. We'd have to do the structural recursion on the RHS
 *               in an *outer* loop.
 *
 *            -> We *can* however measure the number of alternatives up-front.
 *               along with all of our other properties.
 *
 *               So we can indeed allocate correctly.
 *
 *
 *            -> Unfortunately, we do need to know the # of RHS alternatives
 *               before we know the size of the first cubic tree, so we can't allocate
 *               the trailing headers immediately.
 *                 -> Our structural recursion problem again.
 *
 *     -> Alternative would be to describe the tree structure up front,
 *        (or to put all of their headers first) followed by the
 *        actual tree data afterward
 *
 *          -> This also plays better with our allocation structure
 *             (although copy and realloc really isn't so bad)
 *
 *  Okay, so we have:
 *  # is_complete, dims, dims...
 *
 *  if the tree continues, then it has a bitmask set
 *  (just like usual) representing the pixels that have
 *  their own sub-trees
 *
 *  Goal is to be able to sample at all depth levels in O(1) pass.
 *
 *  Following the "dims tree" we have the "samples"
 *     -> This works like normal for complete trees
 *     -> For "complex trees", we expect samples to be laid out
 *        in exactly the order predicted by the bit-sets in the
 *        dims trees 
 *  
 *
 *  void *alternatives;
 *  uint16_t n_alts;
 *  uint16_t n_dims; // If this has high-bit set, bit-sets follow
 *  uint16_t dims[n_dims];
 *  uint64_t descend_bitsets[]; // This is sized depending on dims
 *
 *  // Which means I don't know where to put the follow-ons...
 *  // until after I've finished the "level-1" recursion
 *
 *   // (a) we could build another stack of follow-ons to resume from
 *   // (b) or we can suck it up and do this in two phases
 *           (i) measure all of the dims, notice whether there are any Tuples
 *           (ii) if there are Tuples (w/ unions in them anywhere), then we
 *                append all of our bitsets and do a second sweep descending
 *                into tuples and measuring their bases.
 *
 *   How does the solver use this information?
 *     - If we have this kind of situation, there's a chance that:
 *          First of all, the usual early-exits: Esp. total coverage (w/o obligations)
 *             by any RHS alternative means that we could remove the cubic sub-tree
 *
 *          NOTE 1: It'd be really nice to support this cancellation in the "usual" way
 *                  where we just pop off the contributions we thought we needed from the
 *                  stack
 *
 *                  Unfortunately, that does go against the structural grouping of the RHS
 *
 *          NOTE 2: The solver will go through these, and look for missing coverage. It needs
 *                  to be able to accurately correlate the RHS bits with their related bits
 *                  from the upper-level.
 *
 *                  This implies two things:
 *                    (1) We cannot just lump together all of the RHS alternatives for the 
 *                        inductive problem.
 *                    (2) It might be worth it just to "expand" our LHS basis to include these
 *                        extra bits.
 *                           -> The challenge is to get the right inductive structure
 *
 *   The basic algorithm is that we take a large cube, then:
 *      (i) split it into n-tants
 *      (ii) recursively try to cover those n-tants
 *
 *   Wow, I forget how simple our algorithm was. It's super nice,
 *   and my initial intuition was correct. We can just induct
 *   (carefully) in the solver.
 *
 *   What does the inductive algorithm look like?
 *      (i) start with a good guess
 *      (ii) a sub-problem expands to its pixel when it is covered.
 *           -> So when diving into the complement of this component,
 *              I'd be trying to prove coverage of the whole "sub-pixel"
 *               -> This becomes another exponential problem of its own
 *
 *   So as usual, we take these complementing masks in different combinations.
 *     -> *Every* time we try to solve one of the top-level sub-problems, we descend
 *        into the lower lower problem and try to prove coverage either of the
 *        thing or its complement. 
 *
 *         -> I *think* we do this for each *candidate* solution.
 *
 *         -> So is the original solution actually correct?
 *            -> We just have to be able to correlate the bases so that I
 *               can mask away the proof obligations handled by another alternative
 *
 *         -> I think maybe our original idea was best! 
 *            -> I just have to make sure the masks I use handle the induction correctly
 *
 **/

/**
 * TODO: Create debug print-out for our obligations
 **/

// pop/push
// or save/restore
static void *linear_alloc(size_t sz, size_t align, jl_linear_alloc_t *alloc) {
    size_t index = align_forward(alloc->sz, align);
    if ((index + sz) > alloc->capacity)
        return 0;

    alloc->sz = index + sz;
    return &alloc->buffer[index];
}

static int linear_alloc_init(void *buffer, size_t sz, jl_linear_alloc_t *alloc) {
    if (sz < sizeof(void *))
        return -1;

    *((void **) buffer) = NULL;

    alloc->buffer = (char *)buffer;
    alloc->sz = sizeof(void *);
    alloc->capacity = sz;
    return 0;
}


typedef struct {
    size_t length;
    void *buffer;
} buffer_t;

typedef struct {
    enum maybe_bool status;
    jl_stobligation2_t obligations; // TODO: Try to use more data types if we can
} jl_stresult2_t;

//typedef struct jl_stobl_ll_t {
    //void *obligation;
    //struct jl_stobl_ll_t *next;
//} jl_stobl_ll_t;

jl_stresult2_t subtype_datatype(jl_value_t *x, jl_value_t *y, jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env);

void flip_dim(uint32_t *inout, uint32_t *patt, size_t sz, size_t *volume) {
    //size_t old_popcnt = 0;
    //size_t new_popcnt = 0;
    //for (size_t i = 0; i < sz; i++) {
        //old_popcnt += __builtin_popcount(inout[i]);
        //inout[i] = inout[i] ^ patt[i];
        //new_popcnt += __builtin_popcount(inout[i]);
    //}
    //*volume /= old_popcnt;
    //*volume *= new_popcnt;
}

int check_coverage(jl_stsample_t *lhs, jl_stsample_t *rhs, jl_stobligation2_t *obligations, jl_stenv2_t *env);

static void print_sample_tree(jl_stsample_t *lhs, int indent) {
    uint16_t n_dims = lhs->n_dims;
    uint16_t n_alts = lhs->n_alts;
    uint16_t bvec_sz = lhs->bvec_sz;
    uint16_t subtree_sz = lhs->subtree_sz;
    for (int a = 0; a < n_alts; a++) {
        fprintf(stderr, "%*s", indent, "");
        fprintf(stderr, "alt %d:\n", a);
        for (int d = 0; d < n_dims; d++) {
            fprintf(stderr, "%*s", indent, "");
            fprintf(stderr, "  dim %d (%d): ", d, lhs->dims[d]);
            for (int i = bvec_sz; i-- > 0;) {
                fprintf(stderr, "%08lx", lhs->subtype[a * bvec_sz * n_dims + d * bvec_sz + i]);
            }
            fprintf(stderr, "\n");
            for (int s = 0; s < subtree_sz; s++) {
                if (lhs->subtrees[a * n_dims * subtree_sz + d * subtree_sz + s] == NULL)
                    continue;
                    //break;

                // TODO: Why are our trees... empty sometimes?

                fprintf(stderr, "\n%*s", indent, "");
                fprintf(stderr, "    subtree %d: \n", s);
                print_sample_tree(lhs->subtrees[a * n_dims * subtree_sz + d * subtree_sz + s], indent + 6);
            }
        }
    }
}

int solve_obligations(jl_stobligation2_t *obligations, jl_stenv2_t *env) {

    // Holy cow! I'm finally at the solving stage!
    jl_stsample_t *sample = obligations->rhs;

    uint16_t n_dims = sample->n_dims;
    uint16_t n_alts = sample->n_alts;
    uint16_t bvec_sz = sample->bvec_sz;
    fprintf(stderr, "%d dims %d alts (%d bvec_sz)\n", n_dims, n_alts, bvec_sz);

    // Great, now we're off to the races!
    fprintf(stderr, "checking coverage for LHS:\n");
    print_sample_tree(obligations->lhs, 2);
    fprintf(stderr, "sampled:\n");
    print_sample_tree(obligations->rhs, 2);

    return check_coverage(obligations->lhs, obligations->rhs, obligations, env);
}

static inline void bitset_xor(uint64_t *dst, uint64_t *a, uint64_t *b, size_t sz) {
    for (int i = 0; i < sz; i++) {
        dst[i] = a[i] ^ b[i];
    }
}

static inline void bitset_and(uint64_t *dst, uint64_t *a, uint64_t *b, size_t sz) {
    for (int i = 0; i < sz; i++) {
        dst[i] = a[i] & b[i];
    }
}

static inline bool bitset_equal(uint64_t *a, uint64_t *b, size_t sz) {
    for (int i = 0; i < sz; i++) {
        if (a[i] != b[i])
            return false;
    }
    return true;
}

static inline size_t bitset_popcount(uint64_t *a, size_t sz) {
    size_t count = 0;
    for (int i = 0; i < sz; i++) {
        count += __builtin_popcount(a[i]);
    }
    return count;
}

/**
 * This is... quite a bit of code now with the higher-order support...
 *
 * TODO: If we had a way to disable alternatives, we could simplify this
 *       check dramatically (we'd no longer rely on it for steering the
 *       search).
 **/
size_t best_alternative(jl_stsample_t *lhs, jl_stsample_t *rhs, uint16_t *best_alt, uint64_t *bset) {

    uint16_t n_alts = rhs->n_alts;
    uint16_t n_dims = lhs->n_dims;
    uint16_t bvec_sz = lhs->bvec_sz;
    uint16_t subtree_sz = lhs->subtree_sz;

    if (n_alts == 0)
        return 0;

    size_t max_volume = 0;
    for (int a = 0; a < n_alts; a++) {
        size_t volume = 1; // TODO: float?
        for (int d = 0; d < n_dims; d++) {
            uint64_t *subtype_bset = &rhs->subtype[a * n_dims * bvec_sz + d * bvec_sz];
            bitset_and(bset, subtype_bset, &lhs->subtype[d * bvec_sz], bvec_sz);
            size_t dim_volume = bitset_popcount(bset, bvec_sz);

            for (int s = 0; s < subtree_sz; s++) {
                jl_stsample_t *lhs_subtree = lhs->subtrees[d * subtree_sz + s];
                jl_stsample_t *rhs_subtree = rhs->subtrees[a * n_dims * subtree_sz + d * subtree_sz + s];

                if (lhs_subtree == NULL || rhs_subtree == NULL)
                    continue;

                uint16_t sub_a; // discarded
                dim_volume += best_alternative(lhs_subtree, rhs_subtree, &sub_a, bset);
            }
            volume *= dim_volume;
        }
        if (volume > max_volume) {
            max_volume = volume;
            *best_alt = a;
        }
    }
    return max_volume;
}

static inline bool getbit(uint64_t *bvec, size_t i)
{
    return bvec[i / 64] & (1ull << (i % 64));
}

static inline bool setbit(uint64_t *bvec, size_t i, bool value)
{
    bool old_value = bvec[i / 64] & (1ull << (i % 64));
    if (value)
        bvec[i / 64] |= (1ull << (i % 64));
    else
        bvec[i / 64] &= ~(1ull << (i % 64));
    return old_value;
}

// TODO: Provide optimized implementation
static inline void setbits(uint64_t *bvec, size_t start, size_t end, bool value)
{
    for (size_t i = start; i < end; i++)
        setbit(bvec, i, value);
}

// TODO: Provide optimized implementation
static inline void copybits(uint64_t *dst, uint64_t *src, size_t start, size_t end)
{
    for (size_t i = start; i < end; i++)
        setbit(dst, i, getbit(src, i));
}


        // Okay we've given up both tuple elision and sub-pixel optimization,
        // which I think is for the best.
        //
        // TODO: Let's make sure that we have a graceful reduction for non-distributive
        // tuples. We probably need to detect these up-front that we encountered no
        // LHS unions that we need to distribute over.



// TODO: Make sure that we can still reduce the tuple
//       properly when there are either no LHS union (inner) alternatives
//       or no RHS union alternatives (outer)

/**
 * Rules for elision:
 *   - Tuples with non-distributive dimensions have these eagerly reduced and
 *     they are *not* marked as distributive tuple aggregates
 *   - These also do not participate in the bit-vector for the hyper-cube
 *   - Any *distributive* dimensions of the tuple are represented in full
 **/

/**
 * Step 1: Chose best alternative
 *         -> How is this computed?
 *            We have a new mask, and we need to go through all alternatives and pick the best
 *            one based on volume. This is not complicated by sub-trees (we just need to copy
 *            the result out from the best sub-tree).
 *
 * Step 2: Allocate new mask and copy the bvec from the
 *         best alternative
 *
 * Step 3: while(...) {
 *             take_nth_cartesian_complement();
 *             recursion_entry_point(complement);
 *         }
 *         return true;
 *
 *
 *  TODO: *fuck* I just realized incomplete_dims are a function of the mask
 *             -> so we can't have that pre-computed (volume either)
 **/

/**
 * TODO: Re-write this to:
 *   1. Use our new aggregate vectors - DONE
 *   2. Use a half-plane, quarter-plane algorithm - DONE
 *   3. Use a dimensional index for computing half-planes - DONE
 *
 * Hopefully, things will stay pretty simple even with those improvements.
 * It certainly simplifies the recursion.
 *
 * Wow, even with my memcpy hacks this function is actually *beautiful*
 * Let's see if we can retain the beauty in our new version
 **/
bool take_nth_cartesian_complement(size_t n, uint64_t *bvec, uint64_t *mask, jl_agg_result_t *rhs, size_t *bit_offset)
{
    // mask == C
    rhs = unwrap_aggregate(rhs->results[0]);
    assert(rhs);

    // in_progress = complement_taken
    bool in_progress = false, restore_mask = false;
    for (int i = 0; i < rhs->size; i++) {
        jl_agg_result_t *component = unwrap_aggregate(rhs->results[i]);
        if (!(component && component->is_distributive_tuple && !component->is_distributive_tuple_root))
            continue; // non-distributive dimension

        const size_t component_offset = *bit_offset;
        size_t start = *bit_offset;
        for (int b = 0; b < component->size; b++) {
            size_t end = *bit_offset;
            jl_agg_result_t *subtree = unwrap_aggregate(component->results[b]);
            bool bit_in_progress = false;
            if (subtree && subtree->is_distributive_tuple && !subtree->is_distributive_tuple_root)
                bit_in_progress = take_nth_cartesian_complement(n - dim, bvec, subtree, bit_offset);
            else if (!getbit(mask, *bit_offset))
                bit_in_progress = getbit(bvec, *bit_offset++); // Something set in !C
            else if (!getbit(bvec, *bit_offset++))
                restore_mask = true;

            if (bit_in_progress) {
                setbits(bvec, start, end, false);
                start = *bit_offset;
                in_progress = true;
            }
        }

        if (!in_progress && restore_mask)
            copybits(bvec, mask, component_offset, *bit_offset);
        if (in_progress || restore_mask)
            return in_progress;
    }
    return false;
}

/**
 * TODO: Possibly re-create this for the new scheme
 *       The queue-based design is just rather... bulky
 *
 *       Separating on all sub-trees really isn't so bad.
 *       And neither is "cheating" and using the stack for our queue.
 *       I just needed to see what the "correct" answer would look like.
 **/
int check_coverage(jl_stsample_t *lhs, jl_stsample_t *rhs, jl_stobligation2_t *obligations, jl_stenv2_t *env) {
    jl_stsample_t *sample = rhs;
    uint64_t *demand_bitset = lhs->subtype;

    uint16_t n_dims = lhs->n_dims;
    uint16_t n_alts = sample->n_alts;
    uint16_t bvec_sz = lhs->bvec_sz;
    uint16_t subtree_sz = lhs->subtree_sz;

    uint64_t *bset = (uint64_t *)linear_alloc(bvec_sz * sizeof(uint64_t), alignof(uint64_t), env->alloc);

    uint16_t best_alt;
    size_t max_volume = best_alternative(lhs, rhs, &best_alt, bset);

    // TODO: total_volume optimization
    // TODO: Any incompletely covered dimension optimization (done at top-level only)

    if (max_volume == 0 && lhs == obligations->lhs)
        return 0; // Base case

    jl_stsample_t **saved_subtrees = (jl_stsample_t **)linear_alloc(
        subtree_sz * sizeof(jl_stsample_t *), alignof(jl_stsample_t *), env->alloc);

    /**
     * TODO: Re-factor this to some kind of useful bit-vector struct?
     **/
    for (int d = 0; d < n_dims; d++) {
        memcpy(saved_subtrees, &lhs->subtrees[d * subtree_sz], subtree_sz * sizeof(jl_stsample_t *));
        memset(&lhs->subtrees[d * subtree_sz], 0, subtree_sz * sizeof(jl_stsample_t *));

        uint64_t *subtype_bset = &sample->subtype[best_alt * n_dims * bvec_sz + d * bvec_sz];
        uint64_t *demand_bset = &demand_bitset[d * bvec_sz];
        bitset_and(bset, subtype_bset, demand_bset, bvec_sz);
        if (!bitset_equal(bset, demand_bset, bvec_sz)) {

            // Check that the complement of the dimension is covered.
            bitset_xor(demand_bset, demand_bset, bset, bvec_sz);
            // TODO: This bitset_xor is the higher-level one

            // TODO: The demand_bitset here is always the top-level one
            if (!check_coverage(obligations->lhs, obligations->rhs, obligations, env))
                return 0;

            // Undo complement operation to restore full dimension
            bitset_xor(demand_bset, demand_bset, bset, bvec_sz);
        }
        // TODO: Do half-plane, quarter-plane instead
        // TODO: Clean up this sloppy masking

        memcpy(&lhs->subtrees[d * subtree_sz], saved_subtrees, subtree_sz * sizeof(jl_stsample_t *));
        memcpy(bset, demand_bset, bvec_sz * sizeof(uint64_t));
        memset(demand_bset, 0, bvec_sz * sizeof(uint64_t));

        /**
         * Our problem is that when I recurse over the bit-sets above, I technically
         * want to exclude the subtrees that I'm handling here
         **/
        for (int i = 0; i < subtree_sz; i++) {
            if (lhs->subtrees[d * subtree_sz + i] == NULL)
                continue;
                //break;

            if (!check_coverage(lhs->subtrees[d * subtree_sz + i],
                        rhs->subtrees[best_alt * n_dims * subtree_sz + d * subtree_sz + i], obligations, env))
                return 0;
        }
        memcpy(demand_bset, bset, bvec_sz * sizeof(uint64_t));
    }

    return 1; // Coverage was proven!
}

/**
 *
 * Next steps:
 *   1. Higher-order bits trees -> DONE
 *   2. Type-vars
 *   3. Invariant datatypes
 *
 *   -> That's basically all we need for subtyping.
 *
 * The plan now is to keep the messy-ness and hack together
 * enough structure to see what we need for general type-vars.
 *
 * Then, once that's clear, we start doing major rip-up to:
 *   (1) Fix our inductive subtyping organization
 *   (2) Plug up any bugs that I didn't think about/test carefully
 *           (esp. allocation, masking, etc.)
 *   (3) Simplify/reduce the code.
 *
 * One candidate we should *strongly* consider is a uniform
 * data-structure that represents sub-trees and dimensions 
 * the same.
 *
 * I'm not sure how much that simplifies our existing code, since
 * the HO is in the structure of the problem, but we could:
 *   -> Adopt a very dumb strategy for how we walk alternatives, e.g. by "bit"
 *   -> Save a lot of effort once we start adding "indeterminate" solutions
 *
 **/


// bvec[rhs_alt_i][param_j][lhs_alt_k]
typedef struct {
    uint16_t i;
    uint16_t j;
    uint16_t k;
    uint16_t subtree;
} jl_stsample_index_t;

/**
 * Next TODO is to make all of these return our new result type
 *
 *      and to decide how we're going to handle that pesky hyper-cube vector for TUPLE's
 **/

jl_small_result_t nonunion_subtype(jl_value_t *x, jl_value_t *y, jl_stsample_t *lhs, jl_stsample_t *rhs,
                                jl_stsample_index_t *i,
                                jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env);
jl_small_result_t unwrap_lhs(jl_value_t *x, jl_value_t *y, jl_stsample_t *lhs, jl_stsample_t *rhs,
                          jl_stsample_index_t *i,
                          jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env);
jl_small_result_t unwrap_rhs(jl_value_t *x, jl_value_t *y, jl_stsample_t *lhs, jl_stsample_t *rhs,
                          jl_stsample_index_t *i,
                          jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env);

bool lhs_covered(jl_stsample_t *lhs);

/**
 * Gives an out buffer
 */
JL_DLLEXPORT jl_small_result_t jl_subtype_datatype(jl_value_t *x, jl_value_t *y) {
    static const size_t CAPACITY = 4096;
    char *buffer = (char *)malloc(CAPACITY);
    jl_linear_alloc_t alloc;
    linear_alloc_init(buffer, CAPACITY, &alloc);

    jl_stenv2_t env = { 0, 0, &alloc };
    jl_varenv_t x_env = { NULL, RIGID };
    jl_varenv_t y_env = { NULL, FLEXIBLE };
    
    jl_small_result_t result = unwrap_lhs(x, y, NULL, NULL, NULL, x_env, y_env, &env);
    /*jl_stresult2_t result = subtype_datatype(x, y, x_env, y_env, &env);*/
    if (!is_determinate(result)) {
        fprintf(stderr, "Solving obligations...\n");
        /**
         * TODO: Apply solver (gray code induction)
         * TODO RIGHT NOW fix obligations
         **/
        //int is_subtype = solve_obligations(&result.obligations, &env);
        //result.status = (is_subtype) ? TRUE : FALSE;
    }

    fprintf(stderr, "Allocated %zu bytes\n", alloc.sz);

    return result;
}

void allocate_sample_tree(jl_stsample_t *sample, jl_datatype_t *dx, jl_value_t *y, jl_stenv2_t *env);
void sample_tuple_subtype(jl_datatype_t *dx, jl_value_t *y, jl_stsample_t *lhs, jl_stsample_t *rhs,
                          jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env);

/**
 * Okay, we need to collapse the sampling hierarchy.
 *
 * Right now, I do this:
 *
 *   - We unwrap the LHS union eagerly (AND - LHS)
 *      - Sample each RHS *alternative* (OR - RHS)
 *          - in each component (AND - both sides)
 *             - against each LHS alternative (AND - LHS)
 *
 * This works, but the down-side is that there are wrappers
 * in the tuple that we have to deal with (UnionAlls).
 *
 * It's also awkward because the data-flow is distributive.
 *
 * In principle, what happens is that at the deeper level I
 * sample ALL of the LHS components against ALL of the RHS
 * components in the usual way, except that I record these
 * into a bit-sample-tree as things go along.
 * 
 *   -> This is exactly distributive reasoning.
 *   -> We relax that requirement that ALL LHS samples are
 *      covered, instead allowing for any "useful" sub-set
 *      of samples to accumulate.
 *   -> If we get full-coverage we just report TRUE.
 *   -> All other ordering stays the same.
 *
 * So, we should pass down a "distribution allowed" flag and
 * a sub-tree + indexing objects, then we pass back a volume
 * and a set of samples. Nice!
 * 
 *    Sounds correct to me!
 **/

/**
 * Next thing to reflect on:
 *    - Whether to pre-allocate LHS/RHS tree or not
 **/

/**
 * Sample LHS will unwrap the LHS unions and do the actual sampling
 *
 * i = the component
 * j = the RHS alternative
 * k = the alternative of the LHS component
 *
 * TODO: Would this be simpler if we didn't group by RHS alternative at the top?
 * TODO: Full recursion (with simple identity check for grounding)
 *
 * As terrible as this was to write, it's actually quite decent structurally.
 **/
void sample_lhs(jl_stsample_t *lhs, jl_stsample_t *rhs, jl_stsample_index_t *i, jl_value_t *xi, jl_value_t *yi,
                jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env) {
    /**
     * Sample across the LHS alternatives
     **/
    if (jl_is_uniontype(xi)) {
        jl_uniontype_t *uxi = (jl_uniontype_t *)xi;
        sample_lhs(lhs, rhs, i, uxi->a, yi, x_env, y_env, env);
        sample_lhs(lhs, rhs, i, uxi->b, yi, x_env, y_env, env);
        return;
    } else if (jl_is_unionall(xi)) {
        // TODO: pop depending on results
        jl_unionall_t *uaxi = (jl_unionall_t *)xi;
        jl_varbinding_t *vb = (jl_varbinding_t *)linear_alloc(
            sizeof(jl_varbinding_t), alignof(jl_varbinding_t), env->alloc);
        *vb = (jl_varbinding_t) {
            /* var */ uaxi->var,
            /* id */ 0, // does not count toward var_cnt
            /* kind */ RIGID,
            /* inv_depth */ env->inv_depth,
            /* prev */ x_env.vars,
        };
        x_env.vars = vb;
        return sample_lhs(lhs, rhs, i, uaxi->body, yi, x_env, y_env, env);
    }

    if (jl_is_datatype(xi) && jl_is_tuple_type(xi)) {
        /**
         * This is actually a copy of the `sample_rhs` logic, if
         * we do it properly.
         **/

        /**
         * Always allocate the LHS tree, regardless
         * of whether we use it - TODO: optimize
         **/
        jl_datatype_t *dxi = (jl_datatype_t *)xi;
        uint16_t subtree_sz = lhs->subtree_sz;
        jl_stsample_t **lhs_subtrees = &lhs->subtrees[i->j * subtree_sz];
        if (lhs_subtrees[i->subtree] == NULL) {
            lhs_subtrees[i->subtree] = (jl_stsample_t *)linear_alloc(
                    sizeof(jl_stsample_t), alignof(jl_stsample_t), env->alloc);

            allocate_sample_tree(lhs_subtrees[i->subtree], dxi, NULL, env); 
        }

        /**
         * TODO: It'd be preferable *not* to always allocate this
         *       but that'd require a smarter check_coverage that
         *       knows a NULL RHS covers an empty LHS
         **/
        uint16_t n_dims = lhs->n_dims;

        jl_stsample_t **rhs_subtrees = &rhs->subtrees[i->i * n_dims * subtree_sz + i->j * subtree_sz];
        if (rhs_subtrees[i->subtree] == NULL) {
            rhs_subtrees[i->subtree] = (jl_stsample_t *)linear_alloc(
                sizeof(jl_stsample_t), alignof(jl_stsample_t), env->alloc);

            allocate_sample_tree(rhs_subtrees[i->subtree], dxi, yi, env); 
        }

        if (jl_is_datatype(yi) && jl_is_tuple_type(yi)) {
            if (jl_nparams(xi) != jl_nparams(yi))
                return; // TODO: Be very mindful of this.

            fprintf(stderr, "HIGHER ORDER sampling (%d, %d, %d) subtree: %d\n", i->i, i->j, i->k, i->subtree);
            jl_(xi);
            jl_(yi);


            /**
             * Hooray! That's the higher-order sampling written.
             *
             * Follow-up with:
             *   (1) For-all variables + Thoughts about ground types, etc.
             *   (2) Solve over existential variables
             *   (3) Solve for "diagonality"
             *
             * Okay, so sub-typing is proving *complicated*. I think it is _solvably_ complicated
             * for Wednesday (maybe), but intersection is almost certainly going to push me into
             * next week.
             *
             * That might be okay... But I *really* wanted to land this in March.
             *    A. Land sub-typing without intersection improvements
             *    B. Wait to reveal sub-typing until we have intersection *and*
             *       jl_verify_timings improvements?
             *
             * The fact of the matter is there's simply quite a bit of work left
             * to massage this thing into place.
             *
             *  -> Intersection does *not* care about distributivity, but the type-var mess is
             *     even worse, I think.
             **/
            sample_tuple_subtype(dxi, (jl_value_t *)yi,
                                 lhs_subtrees[i->subtree], rhs_subtrees[i->subtree],
                                 x_env, y_env, env);
        }

        i->subtree++;
        return;
    }

    fprintf(stderr, "\n\nsample_lhs (%d, %d, %d)\n", i->i, i->j, i->k) ;
    jl_(xi);
    jl_(yi);

    // Don't recurse on conspicuously mis-matched pairs, since we
    // don't handle those correctly yet.
    //
    // TODO: Un-fold of our subtyping logic correctly.
    if ((jl_is_datatype(xi) && jl_is_tuple_type(xi)) || (jl_is_datatype(yi) && jl_is_tuple_type(yi)))
        return;

    jl_stresult2_t result = subtype_datatype(xi, yi, x_env, y_env, env);

    // TODO: Maybe zero any 0-dimension tuples
    //        -> Ideally this would happen *before* our separability check
    // TODO: Don't forget about the "full coverage" fast path

    /**
     * If samples is adjusted to be at the beginning of the right period,
     * then it's this
     **/
    if (result.status == TRUE) {
        uint16_t bvec_sz = rhs->bvec_sz;
        uint16_t n_dims = rhs->n_dims;
        uint64_t *bvec = &rhs->subtype[i->i * n_dims * bvec_sz + i->j * bvec_sz]; // &out->subtype[i.i][i.j][0]

        bvec[i->k / 64] |= (1ull << (i->k % 64));

        uint64_t *bvec2 = &lhs->subtype[i->j * bvec_sz]; // &out->subtype[i.j][0]
        bvec2[i->k / 64] |= (1ull << (i->k % 64));
    } else if (result.status == INDETERMINATE) {
        //// TODO: Re-factor
        //uint16_t bvec_sz = out->bvec_sz;
        //uint16_t n_dims = out->n_dims;
        //uint64_t *bvec = &out->indeterminate[i->i * n_dims * bvec_sz + i->j * bvec_sz]; // &out->subtype[i.i][i.j][0]
        //bvec[i->k / 64] |= (1ull << (i->k % 64));

        //jl_stobligation2_t **obligation_tail = &out->obligations[i->i * n_dims + i->j];
        //while (*obligation_tail != NULL) {
            //// TODO: This is O(N^2) instead of O(N)
            //obligation_tail = &(*obligation_tail)->next;
        //}
        //*obligation_tail = (jl_stobligation2_t *)linear_alloc(
                //sizeof(jl_stobligation2_t), alignof(jl_stobligation2_t), env->alloc);

        //// TODO: This is kind of silly, because the top-level subtyping never returns
        ////       this with a link.
        //**obligation_tail = result.obligations;
    }

    i->k += 1;
}

/**
 * TODO: I'm pretty this definition is broken for
 *       Union-Union comparisons so I need to figure out
 *       how to flatten all of these functions into one.
 *
 *       -> Thinking about what I would do if I had
 *       closures might help with that.
 **/


/**
 * Honestly, we could probably give a closure to count_union_components
 *
 * i = the component
 * j = the RHS alternative
 * k = the alternative of the LHS component
 **/
void sample_rhs(jl_stsample_t *lhs, jl_stsample_t *rhs,
        jl_stsample_index_t *i, jl_datatype_t *dx,
        jl_value_t *y, jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env) {
    //fprintf(stderr, "\n\nsampling rhs\n");
    //jl_(dx);
    //jl_(y);


    /**
     * This is splitting at a RHS leaf (among alternatives)
     **/
    if (jl_is_uniontype(y)) {
        jl_uniontype_t *uy = (jl_uniontype_t *)y;
        sample_rhs(lhs, rhs, i, dx, uy->a, x_env, y_env, env);
        sample_rhs(lhs, rhs, i, dx, uy->b, x_env, y_env, env);
        return;
    } else if (jl_is_unionall(y)) {
        // TODO: pop depending on results
        jl_unionall_t *uay = (jl_unionall_t *)y;
        jl_varbinding_t *vb = (jl_varbinding_t *)linear_alloc(
            sizeof(jl_varbinding_t), alignof(jl_varbinding_t), env->alloc);
        *vb = (jl_varbinding_t) {
            /* var */ uay->var,
            /* id */ env->var_cnt++,
            /* kind */ FLEXIBLE,
            /* inv_depth */ env->inv_depth,
            /* prev */ y_env.vars,
        };
        y_env.vars = vb;
        return sample_rhs(lhs, rhs, i, dx, uay->body, x_env, y_env, env);
    } else if (jl_is_datatype(y) && jl_is_tuple_type(y)) {
        /**
         * Then in our datatype confirmation we
         * recurse with our special tree-sampling.
         **/

        if (jl_nparams(dx) != jl_nparams(y)) {
            // TODO: This can leave the LHS un-allocated *sigh*
            //          -> For example, if the RHS has no alternatives at all...
            i->i += 1;
            return; // TODO: Varargs, etc. - also index more carefully
        }

        /**
         * TODO: Lift dims to outer-level?
         **/
        for ((i->j)=0; (i->j) < rhs->n_dims; (i->j)++) {
            jl_value_t *xi = jl_tparam(dx, i->j);
            jl_value_t *yi = jl_tparam(y, i->j);

            i->k = 0;
            i->subtree = 0;
            sample_lhs(lhs, rhs, i, xi, yi, x_env, y_env, env); // This could do advancing if it had a bit *and* word index
        }

        // If not a union type, then we increment when done
        i->i += 1;
    } else {
        // Ignore types that don't match
    }
}

/**
 *
 * I want to check right before entering the recursive
 * function that I have the right arrays allocated
 *   -> LHS in particular may not need allocation.
 *
 **/
/**
 * If y is provided, this returns a tree sized appropriately for
 * sampling its alternatives
 *
 *  TODO: Optimize for reduced case when n_alts = 1?
 *  TODO: Optimize by allocating/filling both trees together?
 *           -> Maybe strip some data from the RHS
 *              that's already in the LHS
 *
 *  TODO: I *hate* this function because it has to be incredibly
 *        predictive over distant parts of the code.
 **/
void allocate_sample_tree(jl_stsample_t *sample, jl_datatype_t *dx, jl_value_t *y, jl_stenv2_t *env) {
    // TODO: Maybe pull allocation of header in

    uint16_t n_dims = jl_nparams(dx);
    uint16_t n_alts = y ? jl_count_tuples(y) : 1;

    /**
     * TODO: Remove `dims`, and check for coverage at some point instead?
     **/
    sample->dims = (uint16_t *)linear_alloc(
            n_dims * sizeof(uint16_t), alignof(uint16_t), env->alloc);

    uint16_t max_dim = 0;
    uint16_t subtree_sz = 0;
    for (int i=0; i < n_dims; i++) {
        uint16_t dim = jl_count_nontuples(jl_tparam(dx, i));
        if (dim > max_dim)
            max_dim = dim;
        sample->dims[i] = dim;

        size_t subtrees = jl_count_tuples(jl_tparam(dx, i));
        if (subtrees > subtree_sz)
            subtree_sz = subtrees;
    }
    uint16_t bvec_sz = (max_dim + 63) / 64;

    sample->n_dims = n_dims;
    sample->n_alts = n_alts;
    sample->bvec_sz = bvec_sz;
    sample->subtree_sz = subtree_sz;

    sample->subtype = (uint64_t *)linear_alloc(
            n_alts * n_dims * bvec_sz * sizeof(uint64_t), alignof(uint64_t), env->alloc);
    memset(sample->subtype, 0,
           n_alts * n_dims * bvec_sz * sizeof(uint64_t));

    sample->subtrees = (jl_stsample_t **)linear_alloc(
            n_alts * n_dims * subtree_sz * sizeof(jl_stsample_t *), alignof(jl_stsample_t *), env->alloc);
    memset(sample->subtrees, 0,
            n_alts * n_dims * subtree_sz * sizeof(jl_stsample_t *));

    //return sample;
}

void sample_tuple_subtype(jl_datatype_t *dx, jl_value_t *y, jl_stsample_t *lhs, jl_stsample_t *rhs,
                          jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env) {
    //fprintf(stderr, "\n\nsample_tuple_subtype on\n");
    //jl_(dx);
    //jl_(y);

    jl_stsample_index_t i = { 0, 0, 0, 0 };
    sample_rhs(lhs, rhs, &i, dx, y, x_env, y_env, env);
}

jl_small_result_t unwrap_rhs(jl_value_t *x, jl_value_t *y, jl_stsample_t *lhs, jl_stsample_t *rhs,
                          jl_stsample_index_t *i,
                          jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env) {
    if (jl_is_unionall(y)) {

        /** from sample_rhs (1) **/ 

        // TODO: pop depending on results
        jl_unionall_t *uay = (jl_unionall_t *)y;
        jl_varbinding_t *vb = (jl_varbinding_t *)linear_alloc(
            sizeof(jl_varbinding_t), alignof(jl_varbinding_t), env->alloc);
        *vb = (jl_varbinding_t) {
            /* var */ uay->var,
            /* id */ env->var_cnt++,
            /* kind */ FLEXIBLE,
            /* inv_depth */ env->inv_depth,
            /* prev */ y_env.vars,
        };
        y_env.vars = vb;
        return unwrap_rhs(x, uay->body, lhs, rhs, i, x_env, y_env, env);
    } else if (jl_is_uniontype(y)) {
        jl_uniontype_t *uy = (jl_uniontype_t *)y;

        /** from subtype_datatype (0) - if !datatype(x) || nparams == 0 **/
        jl_small_result_t a_result = unwrap_rhs(x, uy->a, lhs, rhs, i, x_env, y_env, env);
        if (is_true(a_result)) return a_result;

        jl_small_result_t b_result = unwrap_rhs(x, uy->b, lhs, rhs, i, x_env, y_env, env);
        if (is_true(b_result)) return b_result;

        if (!is_determinate(a_result)) return a_result;
        if (!is_determinate(b_result)) return b_result;

        return wrap_boolean_result(true, 0); // TODO: Size
        //return (jl_stresult2_t) { FALSE, {} };
    }

    jl_small_result_t result = nonunion_subtype(x, y, lhs, rhs, i, x_env, y_env, env);
    /**
     * TODO: Allow returning a TRUE result when all the components of an
     *       alternative are covered. For now, we only support INDETERMINATE.
     **/

    if (!is_determinate(result)) 
        i->i += 1; // Indeterminate result was stored in our tree (implicitly)

    /**
     *
     * TODO: Support "pixel" optimization(s), with either the caller or callee doing
     *       sampling clean-up, if necessary.
     *
     **/

    return result;
}

// unwrap_lhs -> unwrap_rhs -> subtype

jl_small_result_t unwrap_lhs(jl_value_t *x, jl_value_t *y, jl_stsample_t *lhs, jl_stsample_t *rhs,
                          jl_stsample_index_t *i,
                          jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env) {
    if (jl_is_unionall(x)) {
        /** from sample_lhs (2) **/

        // TODO: pop depending on results
        jl_unionall_t *uax = (jl_unionall_t *)x;
        jl_varbinding_t *vb = (jl_varbinding_t *)linear_alloc(
            sizeof(jl_varbinding_t), alignof(jl_varbinding_t), env->alloc);
        *vb = (jl_varbinding_t) {
            /* var */ uax->var,
            /* id */ 0, // does not count toward var_cnt
            /* kind */ RIGID,
            /* inv_depth */ env->inv_depth,
            /* prev */ x_env.vars,
        };
        x_env.vars = vb;
        return unwrap_lhs(uax->body, y, lhs, rhs, i, x_env, y_env, env);
    } else if (jl_is_uniontype(x)) {
        /** from sample_lhs (2) **/
        jl_uniontype_t *ux = (jl_uniontype_t *)x;

        /**
         * Our out-going recursion sets INDETERMINATE whenever it did sampling, so we
         * short-circuit here in the usual way.
         **/
        jl_small_result_t a_result = unwrap_lhs(ux->a, y, lhs, rhs, i, x_env, y_env, env);
        if (is_false(a_result)) return a_result;
        jl_small_result_t b_result = unwrap_lhs(ux->b, y, lhs, rhs, i, x_env, y_env, env);
        if (is_false(b_result)) return b_result;

        if (!is_determinate(a_result)) return a_result;
        if (!is_determinate(b_result)) return b_result;

        return wrap_boolean_result(true, 0); // TODO: Size
    }

    /**
     * The LHS is a tuple and the RHS is a union-of-tuples
     *
     * Tuple distributivity: Allocate a "sample-tree" to record the coverage
     * of the tuples components by various RHS alternatives.
     *
     * TODO: Factor out into separate function
     **/
    if (jl_is_datatype(x) && jl_is_tuple_type(x)) { //&& jl_is_uniontype(y)) {

        /**
         * TODO: If just one (compatible) tuple, we can return TRUE directly.
         **/

        bool is_root = !lhs;

        jl_datatype_t *dx = (jl_datatype_t *)x;
        if (lhs && (lhs->subtrees[i->j * lhs->subtree_sz + i->subtree] != NULL)) {
            lhs = lhs->subtrees[i->j * lhs->subtree_sz + i->subtree];
        } else {
            jl_stsample_t *new_lhs = (jl_stsample_t *)linear_alloc(
                    sizeof(jl_stsample_t), alignof(jl_stsample_t), env->alloc);
            allocate_sample_tree(new_lhs, dx, NULL, env); 

            if (lhs)
                lhs->subtrees[i->j * lhs->subtree_sz + i->subtree] = new_lhs;
            lhs = new_lhs;
        }

        if (rhs && (rhs->subtrees[i->i * rhs->n_dims * rhs->subtree_sz + i->j * rhs->subtree_sz + i->subtree] != NULL)) {
            rhs = rhs->subtrees[i->i * rhs->n_dims * rhs->subtree_sz + i->j * rhs->subtree_sz + i->subtree];
        } else {
            jl_stsample_t *new_rhs = (jl_stsample_t *)linear_alloc(
                    sizeof(jl_stsample_t), alignof(jl_stsample_t), env->alloc);
            allocate_sample_tree(new_rhs, dx, y, env); 

            if (rhs)
                rhs->subtrees[i->i * rhs->n_dims * rhs->subtree_sz + i->j * rhs->subtree_sz + i->subtree] = new_rhs;
            rhs = new_rhs;
        }

        // TODO: If this sample wasn't used, pop the allocation
        jl_stsample_index_t index = { 0, 0, 0, 0 };
        jl_small_result_t result = unwrap_rhs(x, y, lhs, rhs, &index, x_env, y_env, env);

        if (i)
            i->subtree += 1;

        //if (is_root) {
            //fprintf(stderr, "Covered? %d\n", lhs_covered(lhs));
            //print_sample_tree(lhs, 2);
            //print_sample_tree(rhs, 2);
        //}

        // Fast path: Check that LHS was covered separably
        if (is_root && !lhs_covered(lhs))
            return wrap_boolean_result(false, 0); // TODO: De-allocate - and support sub-roots

        // TODO RIGHT NOW -> translate obligations
        //result.obligations = (jl_stobligation2_t) { lhs, rhs, NULL };

        //// If there was an "obvious" mis-match then we still might do a "pixel-mark",
        //// so paper over that here. TODO proper "pixel" support.
        //if (!is_root)
            //result.status = INDETERMINATE;

        return result;
    }

    jl_small_result_t result = unwrap_rhs(x, y, lhs, rhs, i, x_env, y_env, env);

    /**
     * If we have something to sample into and we're *not* sampling a tuple.
     **/
    if (lhs && i) {
        assert(is_determinate(result));
        if (is_true(result)) {
            uint16_t bvec_sz = rhs->bvec_sz;
            uint16_t n_dims = rhs->n_dims;
            uint64_t *bvec = &rhs->subtype[i->i * n_dims * bvec_sz + i->j * bvec_sz]; // &out->subtype[i.i][i.j][0]
            uint64_t *bvec2 = &lhs->subtype[i->j * bvec_sz]; // &out->subtype[i.j][0]
            bvec[i->k / 64] |= (1ull << (i->k % 64));
            bvec2[i->k / 64] |= (1ull << (i->k % 64));
        }
        //fprintf(stderr, "Ground sample @ bit %d\n", i->k);
        //jl_(x);
        //jl_(y);
        i->k += 1;
        // TODO: Return a real result...
        //       Think about what's actually going on here.
        return wrap_aggregate_result((jl_agg_result_t*) NULL);
        //return (jl_stresult2_t){ INDETERMINATE, {} };
    }

    return result;
}

/**
 * Output is a LHS sampling tree
 * and a RHS sampling tree
 *
 *  -> And this is just our usual top-level
 **/
jl_small_result_t nonunion_subtype(jl_value_t *x, jl_value_t *y, jl_stsample_t *lhs, jl_stsample_t *rhs,
                                jl_stsample_index_t *i,
                                jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env) {
    /**
     * This function is *only* responsible for T <: U, where neither T nor U are
     * wrapped by Unions nor UnionAlls
     *
     * Currently: 
     *   - Tuple & Tuple
     *   - Ground & Ground
     **/

    /** from sample_rhs (1) **/
    if (jl_is_datatype(x) && jl_is_tuple_type(x) && jl_is_datatype(y) && jl_is_tuple_type(y)) {
        /**
         * Then in our datatype confirmation we
         * recurse with our special tree-sampling.
         **/

        if (jl_nparams(x) != jl_nparams(y)) {
            // TODO: This can leave the LHS un-allocated *sigh*
            //          -> For example, if the RHS has no alternatives at all...
            //
            // TODO: Fix this immediately

            // TODO: Size?
            return wrap_boolean_result(false, 0); // TODO: Varargs, etc. - also index more carefully
        }

        for (int j=0; j < rhs->n_dims; j++) {
            jl_value_t *xi = jl_tparam(x, j);
            jl_value_t *yi = jl_tparam(y, j);

            if (i) {
                i->k = 0;
                i->subtree = 0;
                i->j = j;
            }

            /** Now, we call into our main entry point, as usual (which is just unwrap_lhs). **/
            jl_small_result_t c_result = unwrap_lhs(xi, yi, lhs, rhs, i, x_env, y_env, env);

            // Intentionally neglect the result, so that it can be handled in our
            // solver instead. Is this stupid? Yes.
            //
            // Can be improved by returning early and trimming at the caller.

            //if (c_result.status == FALSE)
                //return c_result;

            /**
             * XXX: Awkward that the return value here isn't terribly meaningful.
             *      I'm measuring a Union{ ... } against a Union{ ... }
             *         -> That could either return INDETERMINATE (meaning partial coverage)
             *              -> But there's no actual result for it to return, since it's
             *                 embedded in the sub-tree
             *
             *         -> or it could return FALSE is absolutely no samples were covered
             *            or TRUE if they were all covered.
             *
             * -> OR, make it the caller's responsibility to clean-up any sampled values
             *
             **/
        }
        return wrap_aggregate_result((jl_agg_result_t *)NULL);
        //return (jl_stresult2_t) { INDETERMINATE, {} };
    }

    /**
     * Ground type handling - extremely basic for now
     **/
    if ((jl_value_t *)x == y)
        return wrap_boolean_result(true, 0); // TODO: Size?
    else
        return wrap_boolean_result(false, 0); // TODO: Size?
}

/**
 * This also becomes a simple bit check, which is super nice!
 *
 * The pathway is becoming clear...
 *
 * We're about to finally have a tuple + (first-order) bounds
 * solver and then we'll just have to add higher-order bounds
 * and all the 'miscellanea' (varargs, Type{T}, etc.)
 **/
bool lhs_covered(jl_stsample_t *lhs) {
    uint16_t n_dims = lhs->n_dims;
    uint16_t bvec_sz = lhs->bvec_sz;
    uint16_t subtree_sz = lhs->subtree_sz;

    for (int i = 0; i < n_dims; i++) {
        uint16_t n_bits = lhs->dims[i];

        // Verify that all dimensions were fully sampled
        for (int b = 0; b < bvec_sz; b++) {
            int first_zero = __builtin_ffsll(~lhs->subtype[i * bvec_sz + b]);
            first_zero = (first_zero == 0) ? 64 : first_zero - 1;
            //fprintf(stderr, "first_zero: %d n_bits: %d\n", first_zero, n_bits);
            if (first_zero < n_bits) {
                fprintf(stderr, "expected %d bits but first_zero at %d\n", n_bits, first_zero);
                return false;
            }
            n_bits -= 64;
        }
        
        // Verify that all sub-trees have been fully sampled
        for (int s = 0; s < subtree_sz; s++) {
            jl_stsample_t *subtree = lhs->subtrees[i * subtree_sz + s];
            if (subtree == NULL) 
                continue;
                //break; // TODO: fix
            if (!lhs_covered(subtree))
                return false;
        }
    }
    return true;
}

jl_stresult2_t subtype_datatype(jl_value_t *x, jl_value_t *y, jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv2_t *env) {

    /**
     * TODO for tomorrow:
     *   I need to make this entry-point accept separate inputs/outputs
     *   for the LHS tree vs. RHS tree. Either:
     *     A. Pre-allocate -> Turn all of the pre-measurement functions
     *        into their recursive versions.
     *     B. Allocate on-the-fly -> Requires weird behavior where the
     *        the LHS is allocated by the first RHS sample
     *
     *   Then, I need to verify that we have full coverage on our
     *   "demand" vector.
     *
     **/
    if (!jl_is_datatype(x) || jl_nparams(x) == 0) {
        // TODO: Proper induction, etc.
        //       (a.k.a. handling "degenerate" unions)
        if (jl_is_uniontype(y)) {
            jl_uniontype_t *uy = (jl_uniontype_t *)y;
            if (subtype_datatype(x, uy->a, x_env, y_env, env).status == TRUE)
                return (jl_stresult2_t) { TRUE, {} };

            if (subtype_datatype(x, uy->b, x_env, y_env, env).status == TRUE)
                return (jl_stresult2_t) { TRUE, {} };

            return (jl_stresult2_t) { FALSE, {} };
        }
        /**
         * Right now I ignore almost everything
         **/
        if ((jl_value_t *)x == y)
            return (jl_stresult2_t) { TRUE, {} };
        else
            return (jl_stresult2_t) { FALSE, {} };
    }
    jl_datatype_t *dx = (jl_datatype_t *)x;

    //uint16_t n_dims = jl_nparams(dx);
    //uint16_t n_alts = jl_count_tuples(y);

    //if (n_alts == 1) {
        //// TODO: Special case - nothing to distribute
    //}

    //jl_stsample_t *sample = (jl_stsample_t *)linear_alloc(
            //sizeof(jl_stsample_t), alignof(jl_stsample_t), env->alloc);

    //sample->n_alts = n_alts;
    //sample->n_dims = n_dims;
    //sample->dims = (uint16_t *)linear_alloc(
            //n_dims * sizeof(uint16_t), alignof(uint16_t), env->alloc);

    //uint16_t max_dim = 0;
    //size_t subtree_sz = 0;
    //for (int i=0; i < n_dims; i++) {
        //sample->dims[i] = jl_count_nontuples(jl_tparam(dx, i));
        //if (sample->dims[i] > max_dim)
            //max_dim = sample->dims[i];

        //size_t subtrees = jl_count_tuples(jl_tparam(dx, i));
        //if (subtrees > subtree_sz)
            //subtree_sz = subtrees;
    //}

    //uint16_t bvec_sz = (max_dim + 63) / 64;
    //sample->bvec_sz = bvec_sz;
    //sample->subtree_sz = subtree_sz;

    /**
     * Allocate and zero bit-vectors
     **/

    //sample->subtype = (uint64_t *)linear_alloc(
            //n_alts * n_dims * bvec_sz * sizeof(uint64_t), alignof(uint64_t), env->alloc);
    //memset(sample->subtype, 0,
            //n_alts * n_dims * bvec_sz * sizeof(uint64_t));

    //sample->indeterminate = (uint64_t *)linear_alloc(
            //n_alts * n_dims * bvec_sz * sizeof(uint64_t), alignof(uint64_t), env->alloc);
    //memset(sample->indeterminate, 0,
            //n_alts * n_dims * bvec_sz * sizeof(uint64_t));

    /**
     * Allocate and zero our obligation chains
     **/

    //sample->obligations = (jl_stobligation2_t **)linear_alloc(
            //n_alts * n_dims * sizeof(jl_stobligation2_t *), alignof(jl_stobligation2_t *), env->alloc);
    //memset(sample->obligations, 0,
            //n_alts * n_dims * sizeof(jl_stobligation2_t *));

    /**
     * Great, time to sample
     **/

    jl_stsample_t *lhs = (jl_stsample_t *)linear_alloc(
            sizeof(jl_stsample_t), alignof(jl_stsample_t), env->alloc);
    jl_stsample_t *rhs = (jl_stsample_t *)linear_alloc(
            sizeof(jl_stsample_t), alignof(jl_stsample_t), env->alloc);

    allocate_sample_tree(lhs, dx, NULL, env); 
    allocate_sample_tree(rhs, dx, y, env); 

    sample_tuple_subtype(dx, y, lhs, rhs, x_env, y_env, env);

    // Fast path:
    //   Check that LHS was covered separably
    if (!lhs_covered(lhs))
        return (jl_stresult2_t) { FALSE, {} };

    // TODO: Volume fast path
    // TODO: Free allocations if proving non-result early

    /**
     * TODO: This now needs to stitch together the lhs and rhs
     **/

    return (jl_stresult2_t) {
        INDETERMINATE, (jl_stobligation2_t) { lhs, rhs, NULL } };


    /**
     * Okay, no eager flattening. We will traverse over-and-over.
     *
     * I need to know:
     *   (a) # of outside RHS unions (alternatives)
     *       -> these solutions will end up in a vector
     *   (b) # of inside LHS unions (for tuples only)
     *   (c) store "volumes" as we go along (again, for tuples only)
     *
     *  We will store this as
     *
     *  struct {
     *      uint64_t free_bitmasks[computed_bitmask_len(dims, n)];
     *      uint64_t conditional_bitmasks[computed_bitmask_len(dims, n)];
     *      jl_value_t **bounds;
     *  } alts[k];
     * 
     * We:
     *   1. Scan LHS to get n_dims and dims - Fill in header
     *   2. Scan RHS and get k - allocate space for bitmasks
     *   3. Sample RHS against LHS
     *       -> Within each RHS, for evidence do we want to scan ahead and over-alloc OR not?
     *           i. If we scan ahead 
     **/

/**
 * UNION node
 *
 *   0. number of RHS alternatives
 *   1. sizes/dimensions of each part of cube
 *   2. bitmasks for evidence-free components
 *   3. bitmasks for evidence-based components
 *   4. evidence for evidence-based components
 *
 *    - (0) -> (1) -> (2 & 3) -> (4)
 *
 *
 *  Which makes this fairly efficient for the common case that
 *  our hyper-cube is evidence-free.
 *
 *  One potential optimization is to skip the conditional bitmasks if
 *  we are completely evidence-free.
 *  
 **/

    /**
     * Okay, either I flatten into a temporary stack-like buffer
     *   or I build a bit-vector to iterate
     *   or we count before-hand and then just let our stack do
     *   the bit-vectoring for us.
     **/
}

/**
 * Let's start planning our "tree":
 *
 *   Every time I do a forall-exists and have:
 *     (1) No closed matches
 *     (2) >2 open matches
 *
 *   I need to add a branch to an "open" match tree
 *
 *   Then, later as conflicts are discovered, we will
 *   filter out branches from the match tree.
 *
 *   If we run out of alternatives, we have a negative
 *   subtyping result.
 *
 *   That simple.
 *
 * KISS Proposal:
 *   - We keep a union-decision tree, which is pointed at
 *     by a linked-list of "new bounds."
 *
 * AND-OR structure:
 *   - In theory, each left Union adds an AND branch and
 *     each right Union adds an OR branch.
 *     - Can we just have the AND be a single node id?
 *     -> The key invariant is to separate the OR branches
 *        so that we know where we can make a decision and where we can't
 *     -> But that can be done just by inheriting the parent branch
 *
 *   - So then you only need to branch when there's a "useful" decision in both ends of the OR
 *
 * Pointers:
 *   - Parent pointers for sure.
 *   (1) How do we look-up new bounds for a type-var that
 *       we need to check for conflicts against?
 *   (2) I think that's all we need.
 * 
 * Interaction/Lifetime:
 *   (1) How soon can we prune/kill the tree? Is it okay to have
 *       1 for the entire subtyping? Does that grow poorly?
 *
 *   (2) What's the interaction across variables?
 * 
 * Finally, does it make sense to have a "candidate" solution the
 * whole time if we actually have a whole suite of possibilities
 * behind us?
 *
 *   -> It would be nice to be able to end early when we completely
 *      kill a necessary branch
 *   -> So yes, we will try to keep "a solution" alive.
 *
 **/

/**
 * TODO: This is quite slow sometimes...
 *       When matching large unions?
 *
 *  If we sort unions a-priori, then we can make
 *  this *much* simpler on ourselves
 *
 *     - Makes it expensive to form unions though
 **/

/**
 * The other merge is going to occasionally yield a TRUE,
 * this one occasionally yields a FALSE
 **/

jl_svec_t *svec_concat(jl_value_t *a, jl_value_t *b) {
    size_t a_sz = jl_is_svec(a) ? jl_svec_len(a) : 1;
    size_t b_sz = jl_is_svec(b) ? jl_svec_len(b) : 1;

    // TODO: Handle jl_nothing

    jl_value_t **a_data = jl_is_svec(a) ? jl_svec_data(a) : &a;
    jl_value_t **b_data = jl_is_svec(b) ? jl_svec_data(b) : &b;

    jl_svec_t *c = jl_alloc_svec_uninit(a_sz + b_sz);
    jl_value_t **c_data = jl_svec_data(c);
    memmove_refs((void**)&c_data[0], (void**)a_data, a_sz);
    memmove_refs((void**)&c_data[a_sz], (void**)b_data, b_sz);

    return c;
}

/**
 * Now, I need to write the OR version
 **/
jl_stresult_t merge_OR_results(jl_stresult_t a, jl_stresult_t b) {
    if (a.result == TRUE || b.result == TRUE)
        return (jl_stresult_t) { TRUE, (jl_stobligation_t) { NULL, NULL } }; // This potentially de-allocates a significant recent stack

    if (a.result == FALSE) return b;
    if (b.result == FALSE) return a;
    
    /**
     * TODO: Handle empty vectors / NOTHING case
     **/
    jl_value_t *val1 = NULL;
    jl_value_t *val2 = NULL;
    JL_GC_PUSH6(&a.condition.required, &a.condition.choice_tree, &b.condition.required, &b.condition.choice_tree,
                &val1, &val2);

    val1 = (jl_value_t *) svec_concat(a.condition.required, a.condition.choice_tree);
    val2 = (jl_value_t *) svec_concat(b.condition.required, b.condition.choice_tree);
    val1 = jl_new_struct(jl_uniontype_type, val1, val2);
    val2 = (jl_value_t *) jl_alloc_svec(0);
    JL_GC_POP();

    jl_stresult_t res = { INDETERMINATE, (jl_stobligation_t) {
        val2, val1,
    } };
    return res;
}

/**
 * `required` is generally a list of bounds that are checked to be compatible
 *     (equivalently, just an ub/lb which have been intersected/merged)
 * `choice_tree` is either a list of bounds or a union to represent a decision point
 *
 *  Representation options:
 *    A. svec(jl_union_type(svec(jl_tvar_t)))
 *
 *            jl_new_typevar(jl_sym_t *name, jl_value_t *lb, jl_value_t *ub);
 *
 *  TODO:
 *    - We also need to account for typevars that are "re-used"
 *    - These do *not* need to be solved for simultaneously.
 *      They are functionally *different* variables.
 **/
jl_stresult_t merge_results(jl_stresult_t a, jl_stresult_t b) {
    if (a.result == FALSE || b.result == FALSE)
        return (jl_stresult_t) { FALSE, (jl_stobligation_t) { NULL, NULL } };

    if (a.result == TRUE) return b;
    if (b.result == TRUE) return a;
    
    //stfprintf(stderr, "MERGING\n");
    //jl_(a.condition.required);
    //jl_(b.condition.required);
    //st_fprintf(stderr, "\n");

    /*assert(a.result == INDETERMINATE);*/
    /*assert(b.result == INDETERMINATE);*/
    /**
     * TODO: GC stuff
     **/

    /**
     * I need an svec or similar for the bounds themselves
     *   (at least for required)
     **/
    size_t a_sz = jl_is_svec(a.condition.required) ? jl_svec_len(a.condition.required) : 1;
    size_t b_sz = jl_is_svec(b.condition.required) ? jl_svec_len(b.condition.required) : 1;

    jl_tvar_bound_t **a_data = (jl_tvar_bound_t **)(jl_is_svec(a.condition.required) ?
            jl_svec_data(a.condition.required) : &a.condition.required);
    jl_tvar_bound_t **b_data = (jl_tvar_bound_t **)(jl_is_svec(b.condition.required) ?
            jl_svec_data(b.condition.required) : &b.condition.required);

    JL_GC_PUSH4(&a.condition.required, &a.condition.choice_tree, &b.condition.required, &b.condition.choice_tree);

    for (int i = 0; i < a_sz; i++) {
        for (int j = 0; j < b_sz; j++) {
            if (a_data[i]->id == b_data[j]->id) {
                /**
                 * Need to scan through and look for UB/LB matches
                 **/

                /**
                 * I believe the x_kind and y_kind here are correct,
                 * since they apply to new variables.
                 *
                 * What is worth studying further is how this can create
                 * an additional obligation on (other) variables
                 *
                 * Is there structure here to exploit, since it's guaranteed
                 * not to include the variable we are checking over?
                 *
                 * Here's an example:
                 *
                 *   Tuple{Ref{Number}, Int32} <: Tuple{Ref{T}, T}
                 *
                 *   -> This creates an obligation for Number to be identical to Number
                 *      -> Number <: T <: Number
                 *         (another reason to do equals)
                 *
                 *   -> But, checking that obligation can in theory produce more constraints?
                 *   Tuple{Ref{Tuple{U, U} where U}, Tuple{Int, Int}} <: Tuple{Ref{T}, T}
                 *       -> This is valid. And all variables are self-contained, so do
                 *          not escape the query.
                 *
                 *
                 *   -> How about this?
                 *
                 *       Tuple{Ref{Tuple{A, A}}, Pair{A, Int}} where A
                 *
                 *       -> In this case, A is the outer-variable
                 *
                 *          -> So the question is... How does A interact during the subtyping?
                 *
                 *       Tuple{K, Ref{Ref{K}} where K, Ref{Int}} where K <: Tuple{Any, Ref{T}, T} where T
                 *
                 *       -> My *intuition* is that the existing variables indeed act
                 *          like forall variables, and so they cannot generate new bounds
                 *
                 *       -> On the other hand, newly-introduced variables indeed behave like normal:
                 *          Tuple{Ref{T} where T <: Number} <: Tuple{
                 *
                 *
                 * So my hypothesis is this:
                 *   - Existing variables are all forall-variables, and behave as such.
                 *   - New variables may be introduced with existential lifetimes.
                 *
                 *   -> So the only "unique" challenge is the scoping problem that we already have.
                 *
                 *      -> In this case though, the variables should be *entirely* closed
                 *         (no interminglers) so we can resolve at the end as usual
                 *
                 **/

                // TODO: Make sure we have coverage for this

                /**
                 * These terms contain (1) free typevars that act as RIGID (i.e. forall)
                 * variables, and (2) bound typevars that take on RIGID/FLEXIBLE status
                 * depending on their loc, as usual.
                 **/
                if ((!a_data[i]->is_upper && b_data[j]->is_upper) ||
                    (a_data[i]->is_upper && !b_data[j]->is_upper)) {

                    /**
                     * TODO: Are we doing our inv_depth covariance check correctly?
                     **/

                    jl_tvar_bound_t *ai = a_data[i];
                    jl_tvar_bound_t *bj = b_data[j];

                    jl_varenv_t x_env = { ai->is_upper ? bj->vars : ai->vars, RIGID };
                    jl_varenv_t y_env = { ai->is_upper ? ai->vars : bj->vars, FLEXIBLE };
                    jl_value_t *lhs = ai->is_upper ? bj->bound : ai->bound;
                    jl_value_t *rhs = ai->is_upper ? ai->bound : bj->bound;
                    /**
                     * TODO: Is it right to re-use our environment?
                     *       Should we reset our var_cnt etc.?
                     **/
                    //jl_stenv_t env = { 0, 0, env->alloc };

                    /**
                     * TODO: Is it right to create a brand new environment?
                     *       Should we at least re-use our linear allocator?
                     **/
                    _Alignas(max_align_t) char buffer[4096];
                    jl_linear_alloc_t alloc;
                    linear_alloc_init(buffer, sizeof(buffer), &alloc);

                    // -1 to disable all covariant early-exits
                    //  TODO: I'm rather dissatisfied with this. It seems
                    //        like it should be possible to match a covariant
                    //        variable against an invariant RHS variable, in
                    //        which case this will be incorrect (but
                    //        only if T has a meaningful LB)
                    //
                    //  It *also* seems like this will be straight up wrong
                    //  for any newly-introduced typevars
                    jl_stenv_t env = { 1000, 0, &alloc };

                    size_t old_sz = env.alloc->sz;
                    jl_stresult_t result = jl_simple_subtype_env(lhs, rhs, x_env, y_env, &env);
                    if (result.result == INDETERMINATE) {
                        // This should be handled as a top-level step that we call into here,
                        // despite having a custom x/y env
                        jl_errorf("Unexpected indeterminate result.");
                    }
                    if (env.alloc->sz != old_sz) {
                        jl_errorf("Linear allocator not correctly restored.");
                    }
                    if (result.result == FALSE) {
                        print_indent();
                        st_fprintf(stderr, "Failed during merging.\n"); 
                        jl_(a.condition.required);
                        jl_(b.condition.required);
                        //st_fprintf(stderr, "FAILED: :(<:)(\n");
                        //jl_(a_data[i]->bound);
                        //jl_(b_data[j]->bound);
                        JL_GC_POP();
                        return (jl_stresult_t) { FALSE, (jl_stobligation_t) { NULL, NULL } };
                    }

                }
            }
        }
    }

    jl_value_t *new_required = NULL;
    jl_value_t *new_choice_tree = NULL;
    {
        JL_GC_PUSH2(&new_required, &new_choice_tree);
        new_required = (jl_value_t *) svec_concat(a.condition.required, b.condition.required);
        new_choice_tree = (jl_value_t *) svec_concat(a.condition.choice_tree, b.condition.choice_tree);
        JL_GC_POP();
    }
    JL_GC_POP();

    jl_stresult_t res = { INDETERMINATE, (jl_stobligation_t) {
        new_required, new_choice_tree
    } };
    return res;
}

jl_stresult_t merge_AND_results(jl_stresult_t a, jl_stresult_t b) {
    if (a.result == FALSE || b.result == FALSE)
        return (jl_stresult_t) { FALSE, (jl_stobligation_t) { NULL, NULL } };

    if (a.result == TRUE) return b;
    if (b.result == TRUE) return a;
    
    jl_value_t *new_required = NULL;
    jl_value_t *new_choice_tree = NULL;
    JL_GC_PUSH6(&a.condition.required, &a.condition.choice_tree, &b.condition.required, &b.condition.choice_tree, &new_required, &new_choice_tree);
    new_required = (jl_value_t *) svec_concat(a.condition.required, b.condition.required);
    new_choice_tree = (jl_value_t *) svec_concat(a.condition.choice_tree, b.condition.choice_tree);
    JL_GC_POP();

    jl_stresult_t res = { INDETERMINATE, (jl_stobligation_t) {
        new_required, new_choice_tree
    } };
    return res;
}

/**
 * Imagine if we can *start* the weekend with a working
 * subtyping algo. Then, we just have to:
 *   1. Add intersection
 *   2. Add distributivity
 *   3. Optimize
 **/

// TODO: Start adding some op variants:
//   - Also what does a primitive intersection type look like?
//
//   - shuttle_subtype: <=>, disjoint, incomparable
//      - depending on which one we want, we might
//        be able to be more efficient.
//      - For now, only consider the needs of subtyping
//   - intersection
// some op-variants (intersection, etc.)
//JL_DLLEXPORT int jl_simple_subtype_env(jl_value_t *x, jl_value_t *y, jl_varkind_t x_kind, jl_varkind_t y_kind, jl_stenv_t *env) {
JL_DLLEXPORT jl_stresult_t jl_simple_subtype_env(jl_value_t *x, jl_value_t *y, jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv_t *env) {
    indent += 2;
    print_indent();
    st_fprintf(stderr, "subtyping simply for (equal: %d):\n", x == y);
    print_indent();
    jl_(x);
    print_indent();
    jl_(y);
    st_fprintf(stderr, "\n");

    if ((x == y) && !(jl_typeis(x, jl_tvar_type) && jl_typeis(y, jl_tvar_type))) {
        indent -= 2;
        return (jl_stresult_t) { TRUE, {} };
    } else if ((x == (jl_value_t*)jl_bottom_type) || (y == (jl_value_t*)jl_any_type)) {
        indent -= 2;
        return (jl_stresult_t) { TRUE, {} };
    }

    //if (jl_typeis(x, jl_tvar_type) || jl_typeis(y, jl_tvar_type)) {
        //jl_(x);
        //jl_(y);
        ////return 
    //}

    /**
     * I am losing my attention span, but I think this is the best path forward:
     *   1. Add RHS types (in whatever hacky way necessary)
     *      -> Start with a tree that mimics the union structure
     *   2. Re-define the L/RHS type system to be cleaner.
     *   3. Depending on how that goes, choose to either:
     *       a. Implement intersection
     *       b. Implement distributivity over tuples
     **/

    /**
     * TODO: For variables declared *within* an invariant section,
     *       we should be able to make them all \forall variables right?
     **/
    //if (jl_typeis(x, jl_tvar_type) && jl_typeis(y, jl_tvar_type)) {
        /**
         * TODO: Re-factor to make smaller
         **/
        //jl_varbinding_t *x_vb = lookup(x_env.vars, (jl_tvar_t *)x);
        //jl_varbinding_t *y_vb = lookup(y_env.vars, (jl_tvar_t *)y);

        //if (x_vb && y_vb) {
            /**
             * TODO: Think about outside-ness very carefully, *and* the way we
             *       introduce type-vars multiple different ways.
             *
             * For example, it seems like we got away with treating variables
             * always RIGID-ly, as long as didn't match them against any
             * FLEXIBLE typevars. Why did that work?
             **/
            ////st_fprintf(stderr, "Checking for outside-ness (x=%s (%p) depth=%d RIGID=%d) (y=%s (%p) depth=%d RIGID=%d)\n",
                            ////(const char*)jl_symbol_name(x_vb->var->name), x_vb, x_vb->inv_depth, x_vb->kind == RIGID,
                            ////(const char*)jl_symbol_name(y_vb->var->name), y_vb, y_vb->inv_depth, y_vb->kind == RIGID
                            ////);
        //}
        //if (x_vb == y_vb) {
            //indent -= 2;
            //return (jl_stresult_t) { TRUE, {} };
        //}

        /**
         * TODO: Re-factor
         **/
        //if ((y_vb != NULL) && (y_vb->kind == FLEXIBLE))
            //tvar_R = 1;

        /*
         * So "outside-ness" is a function of FLEXIBLE being outside of RIGID
         **/
        /**
         * This doesn't match their code at all... (I think)
         **/

        /**
         * It's not the consistency check either...
         *
         * Our bounds are consistent.
         **/

        /**
         * It *must* have to do with how we're introducing
         * our quantifications differently than in the rules
         *
         * We keep our introductions symmetric (which is wrong...)
         *
         * I should be freezing the existing type-vars and keeping
         * the defaults for anything new
         **/

        /**
         * Also, the test I'm failing is not detected as "outside" according to their rules
         *
         * So why is it supposed to fail?
         **/
        //if (x_vb && y_vb &&
            //(x_vb->kind == RIGID) && (y_vb->kind == FLEXIBLE) && (x_vb->inv_depth > y_vb->inv_depth)) {
            /**
             * Why is this valid?
             * This would require the outside variable (y) to be
             * identically a single item (which is totally fine, I'm confused...)
             *
             *   Ref{Ref{\forall X} where X} <: Ref{Ref{\exists Y}} where Y
             *
             *   -> this is only true if X's bounds are both a single-item,
             *      
             *   -> This also *doesn't* solve our Vector{Vector{T}} case...
             *
             *
             **/
            //return (jl_stresult_t) { FALSE, {} };
        //}


        //if (x_vb && y_vb &&
             //((x_vb->kind == FLEXIBLE) && (y_vb->kind == RIGID) && (x_vb->inv_depth < y_vb->inv_depth))) {

            ////st_fprintf(stderr, "Outside-ness detected\n");

            //_Alignas(max_align_t) char buffer[4096];
            //jl_linear_alloc_t alloc;
            //linear_alloc_init(buffer, sizeof(buffer), &alloc);

            //// -1 to disable all covariant early-exits
            ////  TODO: I'm rather dissatisfied with this. It seems
            ////        like it should be possible to match a covariant
            ////        variable against an invariant RHS variable, in
            ////        which case this will be incorrect (but
            ////        only if T has a meaningful LB)
            ////
            ////  It *also* seems like this will be straight up wrong
            ////  for any newly-introduced typevars
            //jl_stenv_t env = { 1000, 0, &alloc };

            //size_t old_sz = env.alloc->sz;
            //jl_stresult_t result;
            ////if (x_vb->kind == RIGID)
                ////result = jl_simple_subtype_env(x_vb->var->ub, x_vb->var->lb, x_env, x_env, &env);
            ////else
            //result = jl_simple_subtype_env(y_vb->var->ub, y_vb->var->lb, y_env, y_env, &env);

            //if (result.result == FALSE) {
                //indent -= 2;
                //return result;
            //}
            
            ////st_fprintf(stderr, "LHS variable is constant, no problem.\n");

            //if (result.result == INDETERMINATE) {
                //jl_errorf("Unexpected indeterminate result.");
            //}
        //}

        /**
         * Now, right down here I want to handle the RIGID/FLEXIBLE case?
         *
         * Yes, R_L rule.
         *
         * Which means jumping straight to comparing UB/LB
         *   (short-circuiting the recursive call below)
         *
         * taking into account their respective inv_depth relationship
         *
         * and then sticking the RIGID term directly into the FLEXIBLE bound
         **/

        /**
         * If a flexible T1 <: rigid T2
         *   T1 outside T2
         *     -> Make sure that T2 is a single type
         *
         * And then paste T2 directly in the bounds for T1
         *
         **/

        //if (x_vb->inv_depth < y_vb->inv_depth) {
            /**
             * TODO: Think about flexibility here.
             **/

            //// Ok, I'm officially fried and making no progress.
            //// Let's grab some food and go home, and then pick this up again.
            ////
            //// I think we need to get this working and then think really
            //// carefully about our inductive assumptions, flexibility, etc.
            ////

            /**
             * TODO: Does this return indeterminate?
             *       It *shouldn't*
             *
             *       Any introduced variables should be fully resolved
             **/

            /**
             * TODO: I need to introduce a wrapper for these
             *       RIGID-referencing, but totally isolated
             *       subtyping calls
             **/

            ////jl_simple_subtype_env(x, tv->lb, x_env, y_env, env);
        //}

        /**
         * TODO: Implement the whole thing here to prevent redundant lookups
         **/

    //} else if (jl_typeis(x, jl_tvar_type) || jl_typeis(y, jl_tvar_type)) {
        /**
         * TODO: Re-factor
         **/
    //}

    if (jl_typeis(x, jl_tvar_type) || jl_typeis(y, jl_tvar_type)) {
        int8_t tvar_R = jl_typeis(y, jl_tvar_type);
        jl_tvar_t *tv = (jl_tvar_t *)(tvar_R ? y : x);
        jl_varbinding_t *vb;
        if (tvar_R) {
            vb = lookup(y_env.vars, (jl_tvar_t *)y);
        } else {
            vb = lookup(x_env.vars, (jl_tvar_t *)x);
        }
        //st_fprintf(stderr, "Checking against typevar: RIGID? %d", vb->kind == RIGID); 
        jl_varkind_t kind = vb ? vb->kind : RIGID; //(R ? y_kind : x_kind); // TODO: RIGID when NULL?
        if (vb == NULL) {
            /**
             * This case is minimally covered, with just 1 test case.
             * (when x is RIGID)
             **/
            //st_fprintf(stderr, "null example %d %d (RIGID: %d)\n", y_kind, x_kind, kind == RIGID);
            //jl_(tv);
        }

        /**
         * RIGID variables always act like their bounds
         **/
        if (kind == RIGID) {
            //st_fprintf(stderr, "Handling RIGID typevar!\n");
            if (tvar_R) {
                indent -= 2;
                return jl_simple_subtype_env(x, tv->lb, x_env, y_env, env);
            } else {
                indent -= 2;
                return jl_simple_subtype_env(tv->ub, y, x_env, y_env, env);
            }
        } else if (kind == FLEXIBLE) {
            //jl_errorf("We're not ready for FLEXIBLE typevars");
            /**
             * TODO: It's probably not worth adding a bound
             *       when the bound you're supplementing is already tighter
             **/

            /**
             * TODO: There are simple cases where it might be worth
             *       skipping creating the tree here
             *
             *       e.g. where a variable is used exactly once
             **/
            //st_fprintf(stderr, "Handling EXISTENTIAL typevar!\n");
            // TODO: We hit this branch way more often than we should have to
            //       for something as simple as Tuple{Ref{Number}, Int32} <: Tuple{Ref{T}, T} where T

            /**
             * TODO RIGHTNOW:
             *   (1) Make sure we root the GC as needed
             *   (2) Maybe add some mechanism for iterating in-place
             **/

            /**
             * For now, skipping the reduction optimization. How does the
             * ID work? It's pretty straight-forward TBH, we just save a
             * generative ID (that we keep in our context) instead of a
             * typevar name.
             *
             * (1) scoping
             *
             *     The basic problem is that every time we go through
             *     a `where` a unique type-var is introduced, but we
             *     can still end up carrying obligations between these.
             *
             *     Consider:
             *
             *       Union{Pair{Int32, Int64}, Pair{Int16, Int32}}
             *           <: Union{Pair{A, C} where A, Pair{B, C} where B} where C
             *
             *           -> The A has to satisfy only "internal" constraints
             *           -> but the C still has more "external" constraints to satisfy
             *
             *    Option (1):
             *       - Give every type-var a generative ID when it enters our environment
             *           -> Effectively uniques all the "A"'s that we encounter
             *
             *    Option (2):
             *       - Try to eliminate the A so that we don't need to keep it around any more.
             *
             *
             * I think (2) does not work in general. Consider:
             *   Triple{Union{A, B}, Union{Pair{Int32, Int16}, Pair{A, C}}, C}
             *     -> Only works in the case that the choice tree of A can be eliminated because:
             *        i. There is a choice that is uniformly better than the alternatives
             *           (i.e. no external obligations leak out from the choice tree at all)
             *       ii. A has no possible solution and so we can fail early.
             *
             *  but there are *definitely* cases where the choices end up inter-mingled
             *  (they are just very rare - TODO: test cases)
             *
             *
             *  Thankfully, (1) and (2) are orthogonal. We can unique-ify and also reduce
             *  as much as possible.
             *
             *     Reduction might work like this:
             *       - Advance until the constraints for A have been satisfied.
             *       - If there are no external (choice) constraints for any other vars,
             *         then we can pop the choice tree (we're done).
             *       - If we are unable to satisfy A, we can fail early.
             *
             *       -> In general, we should always check for a uniformly non-interacting
             *          solution and block further iteration of this group.
             *
             *     This reserves complex inter-twined evaluation to the places where it's necessary.
             *
             **/

            /**
             * TODO: Avoid exposing this to the Julia type-system + GC entirely
             *       (C-only, and all in arenas)
             **/

            /**
             * Check against existing bounds
             **/
            if (tvar_R) {
                // TODO: Have I captured the important skip here?
                if (x == (jl_value_t *)jl_bottom_type) {
                    indent -= 2;
                    return (jl_stresult_t) { TRUE, (jl_stobligation_t) { NULL, NULL } };
                }

                // Y always FLEXIBLE here
                jl_stresult_t result1 = jl_simple_subtype_env(x, tv->ub, x_env, y_env, env);

                if (result1.result == FALSE) {
                    indent -= 2;
                    return (jl_stresult_t) { FALSE, (jl_stobligation_t) { NULL, NULL } };
                }

                jl_value_t *new_required = NULL;
                jl_value_t *new_choice_tree = NULL;
                JL_GC_PUSH4(&result1.condition.required, &result1.condition.choice_tree,
                            &new_required, &new_choice_tree);

                //new_required = (jl_value_t *) jl_new_struct(jl_tvar_bound_type, vb->id, 0, x);

                jl_task_t *ct = jl_current_task;
                jl_tvar_bound_t *bound = (jl_tvar_bound_t *)jl_gc_alloc(ct->ptls, sizeof(jl_tvar_bound_t), jl_tvar_bound_type);
                bound->id = vb->id;
                bound->is_upper = 0;
                bound->bound = x;
                bound->vars = x_env.vars;
                new_required = (jl_value_t*)bound;

                new_choice_tree = (jl_value_t *) jl_alloc_svec(0); // TODO: jl_nothing

                /**
                 * TODO: If we are below the lower-bound, no need to add
                 **/
                jl_stresult_t new_result = { INDETERMINATE, (jl_stobligation_t) {
                    // (jl_value_t *) jl_new_typevar(tv->name, x, (jl_value_t *)jl_any_type),
                    new_required, new_choice_tree
                } };

                /**
                 * Example:
                 *   Pair{Tuple{ ... }, Int} <: Pair{Tuple{Ref{T}, T}, U} where T <: U
                 *
                 *    -> So now, when I match against T and check its
                 *       upper bound, I end up inheriting an obligation
                 *       to compare against Int as well.
                 *
                 * TODO:
                 *   Turn into subtype test (or verify coverage)
                 **/
                JL_GC_POP();
                indent -= 2;
                return merge_results(result1, new_result);
            } else {
                // TODO: Have I captured the important skip here?
                if ((y == (jl_value_t *)jl_any_type) || (vb->inv_depth == env->inv_depth)) {
                    indent -= 2;
                    return (jl_stresult_t) { TRUE, (jl_stobligation_t) { NULL, NULL } };
                }

                // X always FLEXIBLE here
                jl_stresult_t result1 = jl_simple_subtype_env(tv->lb, y, x_env, y_env, env);

                if (result1.result == FALSE) {
                    indent -= 2;
                    return (jl_stresult_t) { FALSE, (jl_stobligation_t) { NULL, NULL } };
                }

                jl_value_t *new_required = NULL;
                jl_value_t *new_choice_tree = NULL;
                JL_GC_PUSH4(&result1.condition.required, &result1.condition.choice_tree,
                            &new_required, &new_choice_tree);
                /**
                 * TODO: If we are above the upper-bound, no need to add
                 **/
                //new_required = (jl_value_t *) jl_new_struct(jl_tvar_bound_type, vb->id, 1, y);
                jl_task_t *ct = jl_current_task;
                jl_tvar_bound_t *bound = (jl_tvar_bound_t *)jl_gc_alloc(ct->ptls, sizeof(jl_tvar_bound_t), jl_tvar_bound_type);
                bound->id = vb->id;
                bound->is_upper = 1;
                bound->bound = y;
                bound->vars = y_env.vars;
                new_required = (jl_value_t*)bound;

                new_choice_tree = (jl_value_t *) jl_alloc_svec(0); // TODO: jl_nothing
                jl_stresult_t new_result = { INDETERMINATE, (jl_stobligation_t) {
                    //(jl_value_t *) jl_new_typevar(tv->name, jl_bottom_type, y),
                    new_required, new_choice_tree
                } };

                JL_GC_POP();
                indent -= 2;
                return merge_results(result1, new_result);
            }
        }
    }

    // XXX: Watch out, this catches type-vars too...
    if (!jl_is_type(x) && !jl_is_type(y)) {
        indent -= 2;
        return (jl_stresult_t) { jl_egal(x, y) ? TRUE : FALSE, {} };
    }

    /**
     * Okay, so now we need to do RHS (contractible) variables.
     *
     * Generally speaking, that just means propagating a few bounds
     * and doing our AND/OR tree carefully!
     *
     * The rest of the logic should be exactly as the LHS variables.
     **/

    /**
     * Options to control the introduction of spurious RHS variables:
     *
     *   (1) Use a fancy control scheme to consider "invariance"
     *       separately from whether something is left vs. right-sided
     *         -> Use inv_depth to opt-in to invariance
     *   (2) Provide a separate "equals" method that compares types
     *       invariantly.
     *
     * (1) is what I do right now
     **/

    // We don't have to add anything to an environment yet
    //  (these are all for-all vars)
    //if (jl_is_unionall(x)) {
        //return jl_simple_subtype_env(jl_unwrap_unionall(x), y, env);
    //} else if (jl_is_unionall(y)) {
        //return jl_simple_subtype_env(x, jl_unwrap_unionall(y), env);
    //}


// (A) Uniquify all of the names, or tie the names to their enclosing scope/env
// (B) Find a way to drop/separate some of these variables, or resolve them early,
//     once we reach their bounds.
//
//     -> We know that once we reach the `where T` we have to be able
//        to choose a path on the tree that has compatible bounds _for T_
//        -> Problem is, that may still be several paths
//           and its expensive to test/encode all the paths that work for T
    /**
     * Might be worth flipping order so that this is simpler:
     * (OR just factoring these logic out to separate functions)
     **/

    // This is our "forall-exists" loop here
    //
    // Ordering here matters:
    //   if I split on Y first, then I am checking whether
    //   for some fixing Y, it's a subtype of all X (totally wrong)
    //
    if (jl_is_uniontype(x)) {
        jl_uniontype_t *ux = (jl_uniontype_t *)x;

        /**
         * Ah, it'd be so nice if subtyping were non-allocating!
         **/
        jl_stresult_t res_a = jl_simple_subtype_env(ux->a, y, x_env, y_env, env);
        if (res_a.result == FALSE) {
            indent -= 2;
            return res_a;
        }

        JL_GC_PUSH2(&res_a.condition.required, &res_a.condition.choice_tree);
        jl_stresult_t res_b = jl_simple_subtype_env(ux->b, y, x_env, y_env, env);
        JL_GC_POP();

        /**
         * We skip the compatibility checks *between* branches here,
         * which is actually correct.
         *
         * TODO: We will still need to recover these branches when "solving" our tree later...
         **/
        indent -= 2;
        return merge_results(res_a, res_b);

        /**
         * So here's an interesting detail:
         *    - We can end up seeing multiple "copies" of a RHS
         *      variable if we go into its where clause from different unions
         *
         * -> We definitely need to handle SCOPING (TODO)
         **/
    } else if (jl_is_uniontype(y)) {
        jl_uniontype_t *uy = (jl_uniontype_t *)y;

        jl_stresult_t res_a = jl_simple_subtype_env(x, uy->a, x_env, y_env, env);
        if (res_a.result == TRUE) {
            indent -= 2;
            return res_a;
        }
        
        JL_GC_PUSH2(&res_a.condition.required, &res_a.condition.choice_tree);
        jl_stresult_t res_b = jl_simple_subtype_env(x, uy->b, x_env, y_env, env);
        JL_GC_POP();

        indent -= 2;
        return merge_OR_results(res_a, res_b);
    }


    /**
     * We can either provide custom order that flips and constant rigidity
     * OR we can flip rigidity and provide custom order
     **/
    if ((jl_is_unionall(x) || jl_is_unionall(y))) {
        // This can happen when we allow a RHS UnionAll that
        // actually appears nowhere
        int8_t R = !jl_is_unionall(x);
        jl_unionall_t *uax = (jl_unionall_t *)(R ? y : x);

        size_t prev_alloc_sz = env->alloc->sz;
        jl_varbinding_t *vb = (jl_varbinding_t *)linear_alloc(
            sizeof(jl_varbinding_t), alignof(jl_varbinding_t), env->alloc);

        if (vb == NULL) {
            jl_errorf("Over-allocated into linear buffer");
        }

        *vb = (jl_varbinding_t) {
            /* var */ uax->var,
            /* id */ 0,
          // TODO: This is what the paper does, but we have a different plan
          //       It doesn't work very well with our bounds accumulation strategy,
          //       *and* it seems like the symmetry of the equality check
          //       makes it largely irrelevant anyway.
            /* kind */ R ? FLEXIBLE : RIGID,
            //[> kind <] R ? y_env.kind : x_env.kind,
            /* inv_depth */ env->inv_depth,
            /* prev */ R ? y_env.vars : x_env.vars,
        };
        if (vb->kind == FLEXIBLE)
            vb->id = env->var_cnt++;

        if (R)
            y_env.vars = vb;
        else
            x_env.vars = vb;
        jl_stresult_t result;
        if (R) {
            result = jl_simple_subtype_env(x, uax->body, x_env, y_env, env);
        } else {
            result = jl_simple_subtype_env(uax->body, y, x_env, y_env, env);
        }

        if (result.result != INDETERMINATE) { // TODO: Maybe check jl_has_free_typevars as well
            env->alloc->sz = prev_alloc_sz; // Pop old allocations (if possible)
            /**
             * TODO: This will leave the stack unpopped for too long
             *       in certain scenarios.
             *
             *  A better solution is to associate a "prev" stack value with the
             *  INDETERMINATE value that we might choose to drop.
             *
             *  *OR* to do this save/restore in other places where we may
             *       drop an INDETERMINATE.
             *
             * Int32 <: Union{A where T, B where T}
             *
             *  -> We'll get existentials from all these variants and then *not*
             *     drop them when we drop them for TRUE/FALSE
             **/
        } else {
            //st_fprintf(stderr, "*not* popping %zu bytes\n", env->alloc->sz - prev_alloc_sz);
        }

        // TODO: Maybe "try" to close scope here?
        //   Depending on dependencies and other variables affected

        // We can at least iterate this sub-group until the results are 
        // compatible.

        indent -= 2;
        return result;
    }

    /**
     * Okay, how do we handle invariant constructors, now?
     * We can either request equality or check both directions
     **/

    if (jl_is_datatype(x) && jl_is_datatype(y)) {
        // Handle datatypes with no parameters
        jl_datatype_t *dx = (jl_datatype_t *)x;
        jl_datatype_t *dy = (jl_datatype_t *)y;
        while (dx->name != dy->name) {
            if (dx == jl_any_type) {
                indent -= 2;
                return (jl_stresult_t) { FALSE, (jl_stobligation_t) { NULL, NULL } };
            }

            dx = dx->super;
        }

        size_t np_x = jl_nparams(dx);
        size_t np_y = jl_nparams(dy);

        if (np_x != np_y) {
            indent -= 2;
            return (jl_stresult_t) { FALSE, (jl_stobligation_t) { NULL, NULL } };
        }

        if (!jl_is_tuple_type(dx))
            env->inv_depth += 1;

        jl_stresult_t result = { TRUE, {} };
        JL_GC_PUSH2(&result.condition.required, &result.condition.choice_tree);
        for (size_t i=0; i < np_x; i++) {
            jl_value_t *xi = jl_tparam(dx, i);
            jl_value_t *yi = jl_tparam(dy, i);

            //st_fprintf(stderr, "checking component %d\n", i);
            //jl_(xi);
            //jl_(yi);
            if (jl_is_tuple_type(dx)) {
                result = merge_results(result, jl_simple_subtype_env(xi, yi, x_env, y_env, env));
            } else {
                result = merge_results(result, jl_simple_subtype_env(xi, yi, x_env, y_env, env));
                // XXX: This check here is *super* important for
                //    NRef(30, Int8) <: NRef(30, Union{Int8, Int32})
                //
                // TODO: Convince myself that there are no other
                //    short-circuits/problematic cases of this kind
                //
                // For example, I think that deferred failure in a union could still
                // cause this to be exponential. And I think instead of checking <: and >:,
                // we should really check (==:)
                // 
                //  *anything* we do twice is extremely suspect.
                //    (and may also contribute to some of our slower subtyping times close to ~1ms)
                //
                if (result.result == FALSE)
                    break;

                /**
                 * TODO: Should this be merge_AND_results?
                 *    -> Also reason about both directions carefully
                 *
                 * FIXME: Reason about this tomorrow.
                 **/

                // We might want to go ahead and switch
                // to forall_equals here
                result = merge_results(result, jl_simple_subtype_env(yi, xi, y_env, x_env, env));
                /**
                 * TODO: Maybe merge forward/backward first?
                 **/

                //if (result.result == FALSE)
                    //break;
            }
            if (result.result == FALSE)
                break;

            //st_fprintf(stderr, "env after (%zu, <:):\n", i);
            //jl_(result.condition.required);
            //st_fprintf(stderr, "\n\n");
            //st_fprintf(stderr, "backwards check for component %d\n", i);

            //jl_kind_t old_y_kind = y_env.kind;
            //jl_kind_t old_x_kind = x_env.kind;
            //y_env.kind = RIGID;
            //x_env.kind = RIGID;


            //st_fprintf(stderr, "env after (%zu, >:):\n", i);
            //jl_(result.condition.required);
            //st_fprintf(stderr, "\n\n");

            // TODO: forall_exists_equal is an optimization the main
            //       algorithm has (i.e. equality)
            //  -> it has a component-wise comparison fast-path
        }

        if (!jl_is_tuple_type(dx))
            env->inv_depth -= 1;

        JL_GC_POP();
        indent -= 2;
        return result;
    }
    /**
     * So, for equality, current subtyping just using it as a means
     * to quickly check unions component-wise
     **/

    /**
     * If I were doing this myself, how would I handle these types?
     * I'd check whether our inv_depth has grown so that I can
     * ignore the check
     **/

    // We're right 50% of the time!
    indent -= 2;
    return (jl_stresult_t) { FALSE, (jl_stobligation_t) { NULL, NULL } };
}

JL_DLLEXPORT int jl_simple_subtype(jl_value_t *x, jl_value_t *y) {
    _Alignas(max_align_t) char buffer[4096];
    jl_linear_alloc_t alloc;
    linear_alloc_init(buffer, sizeof(buffer), &alloc);

    jl_stenv_t env = { 0, 0, &alloc };
    jl_varenv_t x_env = { NULL, RIGID };
    jl_varenv_t y_env = { NULL, FLEXIBLE };
    /*jl_(x);*/
    /*jl_(y);*/
#ifdef USE_TRACY
    TracyCZone(ctx, 1);
#endif
    jl_stresult_t res = jl_simple_subtype_env(x, y, x_env, y_env, &env);
    JL_GC_PUSH2(&res.condition.required, &res.condition.choice_tree);
    // Here's the top-level, where we handle indeterminate answers

    /**
     * TODO: Invent an example with mixed obligations like this...
     *       (actually *quite* rare)
     **/

    if (res.result == INDETERMINATE && jl_is_svec(res.condition.choice_tree) && (jl_svec_len(res.condition.choice_tree) == 0)) {
        // No obligations left to prove
        JL_GC_POP();
        return 1;
    }

    if (res.result == INDETERMINATE) {
        st_fprintf(stderr, "ALERT: Verification needed for choice-tree\n");
        jl_(res.condition.choice_tree);
    }

    JL_GC_POP();

#ifdef USE_TRACY
    TracyCZoneEnd(ctx);
#endif
    return res.result == TRUE;
}

/**
 * TODO: Our iteration scheme still doesn't solve the "dependency" problem
 *       -> I only want to iterate groups that actually might affect
 *          the conflicting result
 **/

/**
 * Still need:
 *   1. Fixed existentials
 *   2. Distributivity
 *   3. Diagonal vars
 *   4. Intersection
 *
 *   5. Optimization
 *       -> Stack-based allocation, etc.
 *
 * That's a long way to go...
 *
 **/

/**
 * Option I. Add branching type-var data to our INDETERMINATE structure
 *        So just save any referenced type-vars with a list of IDs or similar
 * Option II. Add the referenced type-var IDs in the bound itself
 * Option III. Substitute the type-var in the bound we save
 **/

/**
 * Option (I) is quite nice.
 *   i. If return our INDETERMINATE set, then we're not allowed to
 *      pop our LHS env, either.
 *  ii. We could optionally add an jl_has_free_typevars(...) check
 *      to any bounds that would prevent us from popping.
 *
 * This is a good excuse to separate our LHS/RHS envs, so that we
 * count the occurences correctly.
 *
 * It's *also* a good excuse to start designing an arena allocator
 * of some kind for this.
 *   -> We'd probably use a linked-list of geometrically growing nodes?
 *   -> That sounds simple enough to me.
 *       -> Can start with an assert/error check and just a large
 *          static allocation, for simplicity
 * 
 * Neat! We have a path forward!
 *
 * When we test bounds, we just provide our environment(s) as usual!
 **/

#ifdef __cplusplus
}
#endif
