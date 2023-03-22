#include <string.h>
#ifdef _OS_WINDOWS_
#include <malloc.h>
#include <stdalign.h>
#endif
#include "julia.h"
#include "julia_internal.h"
#include "julia_assert.h"

#ifdef __cplusplus
extern "C" {
#endif

// To disable debug printing
#define fprintf(...)
#define jl_(...)

size_t indent = 0;
void print_indent() {
    fprintf(stderr, "%*s", indent, "");
}

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
  **/

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

typedef enum {
    FALSE,
    INDETERMINATE,
    TRUE
} jl_maybe_bool_t;

typedef struct {
    jl_value_t *required;
    jl_value_t *choice_tree;
} jl_stobligation_t;

typedef struct {
    jl_maybe_bool_t result;
    jl_stobligation_t condition;
} jl_stresult_t;

typedef struct {
    jl_varbinding_t *vars;
    jl_varkind_t kind; // TODO: default_kind
} jl_varenv_t;


JL_DLLEXPORT jl_stresult_t jl_simple_subtype_env(jl_value_t *x, jl_value_t *y, jl_varenv_t x_env, jl_varenv_t y_env, jl_stenv_t *env);

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
    
    //fprintf(stderr, "MERGING\n");
    //jl_(a.condition.required);
    //jl_(b.condition.required);
    //fprintf(stderr, "\n");

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
                        fprintf(stderr, "Failed during merging.\n"); 
                        jl_(a.condition.required);
                        jl_(b.condition.required);
                        //fprintf(stderr, "FAILED: :(<:)(\n");
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
    fprintf(stderr, "subtyping simply for (equal: %d):\n", x == y);
    print_indent();
    jl_(x);
    print_indent();
    jl_(y);
    fprintf(stderr, "\n");

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
    int8_t tvar_R = 0;
    if (jl_typeis(x, jl_tvar_type) && jl_typeis(y, jl_tvar_type)) {
        /**
         * TODO: Re-factor to make smaller
         **/
        jl_varbinding_t *x_vb = lookup(x_env.vars, (jl_tvar_t *)x);
        jl_varbinding_t *y_vb = lookup(y_env.vars, (jl_tvar_t *)y);

        if (x_vb && y_vb) {
            /**
             * TODO: Think about outside-ness very carefully, *and* the way we
             *       introduce type-vars multiple different ways.
             *
             * For example, it seems like we got away with treating variables
             * always RIGID-ly, as long as didn't match them against any
             * FLEXIBLE typevars. Why did that work?
             **/
            //fprintf(stderr, "Checking for outside-ness (x=%s (%p) depth=%d RIGID=%d) (y=%s (%p) depth=%d RIGID=%d)\n",
                            //(const char*)jl_symbol_name(x_vb->var->name), x_vb, x_vb->inv_depth, x_vb->kind == RIGID,
                            //(const char*)jl_symbol_name(y_vb->var->name), y_vb, y_vb->inv_depth, y_vb->kind == RIGID
                            //);
        }
        if (x_vb == y_vb) {
            indent -= 2;
            return (jl_stresult_t) { TRUE, {} };
        }

        /**
         * TODO: Re-factor
         **/
        if ((y_vb != NULL) && (y_vb->kind == FLEXIBLE))
            tvar_R = 1;

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


        if (x_vb && y_vb &&
             ((x_vb->kind == FLEXIBLE) && (y_vb->kind == RIGID) && (x_vb->inv_depth < y_vb->inv_depth))) {

            //fprintf(stderr, "Outside-ness detected\n");

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
            jl_stresult_t result;
            //if (x_vb->kind == RIGID)
                //result = jl_simple_subtype_env(x_vb->var->ub, x_vb->var->lb, x_env, x_env, &env);
            //else
            result = jl_simple_subtype_env(y_vb->var->ub, y_vb->var->lb, y_env, y_env, &env);

            if (result.result == FALSE) {
                indent -= 2;
                return result;
            }
            
            //fprintf(stderr, "LHS variable is constant, no problem.\n");

            if (result.result == INDETERMINATE) {
                jl_errorf("Unexpected indeterminate result.");
            }
        }

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

        if (x_vb->inv_depth < y_vb->inv_depth) {
            /**
             * TODO: Think about flexibility here.
             **/

            // Ok, I'm officially fried and making no progress.
            // Let's grab some food and go home, and then pick this up again.
            //
            // I think we need to get this working and then think really
            // carefully about our inductive assumptions, flexibility, etc.
            //

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

            //jl_simple_subtype_env(x, tv->lb, x_env, y_env, env);
        }

        /**
         * TODO: Implement the whole thing here to prevent redundant lookups
         **/

    } else if (jl_typeis(x, jl_tvar_type) || jl_typeis(y, jl_tvar_type)) {
        /**
         * TODO: Re-factor
         **/
        tvar_R = jl_typeis(y, jl_tvar_type);
    }

    if (jl_typeis(x, jl_tvar_type) || jl_typeis(y, jl_tvar_type)) {
        // Prefer resolving FLEXIBLE variables *first*
        //   (TODO: I don't think this definition is strictly correct)
        //
        // TODO: I need to add the R_L rule here, which will handle this correctly
        //       (along with \forall-exists)
        //
        
        /**
         * TODO: This rule is wrong
         **/
        jl_tvar_t *tv = (jl_tvar_t *)(tvar_R ? y : x);
        jl_varbinding_t *vb;
        if (tvar_R) {
            vb = lookup(y_env.vars, (jl_tvar_t *)y);
        } else {
            vb = lookup(x_env.vars, (jl_tvar_t *)x);
        }
        //fprintf(stderr, "Checking against typevar: RIGID? %d", vb->kind == RIGID); 
        jl_varkind_t kind = vb ? vb->kind : RIGID; //(R ? y_kind : x_kind); // TODO: RIGID when NULL?
        if (vb == NULL) {
            /**
             * This case is minimally covered, with just 1 test case.
             * (when x is RIGID)
             **/
            //fprintf(stderr, "null example %d %d (RIGID: %d)\n", y_kind, x_kind, kind == RIGID);
            //jl_(tv);
        }

        /**
         * RIGID variables always act like their bounds
         **/
        if (kind == RIGID) {
            //fprintf(stderr, "Handling RIGID typevar!\n");
            if (tvar_R) {
                if ((vb != NULL) && (vb->inv_depth >= env->inv_depth)) {
                    // TODO: Why do we need this, when the paper's rules do not?
                    // TODO: Remove
                    fprintf(stderr, "Covariant position early-exit (%d >= %d)\n", vb->inv_depth, env->inv_depth);
                    indent -= 2;
                    return (jl_stresult_t) { TRUE, (jl_stobligation_t) { NULL, NULL } };
                }

                indent -= 2;
                return jl_simple_subtype_env(x, tv->lb, x_env, y_env, env);
            } else {
                indent -= 2;
                return jl_simple_subtype_env(tv->ub, y, x_env, y_env, env);
            }
        } else if (kind == FLEXIBLE) {
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
            //fprintf(stderr, "Handling EXISTENTIAL typevar!\n");
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
            //fprintf(stderr, "*not* popping %zu bytes\n", env->alloc->sz - prev_alloc_sz);
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

            //fprintf(stderr, "checking component %d\n", i);
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

            //fprintf(stderr, "env after (%zu, <:):\n", i);
            //jl_(result.condition.required);
            //fprintf(stderr, "\n\n");
            //fprintf(stderr, "backwards check for component %d\n", i);

            //jl_kind_t old_y_kind = y_env.kind;
            //jl_kind_t old_x_kind = x_env.kind;
            //y_env.kind = RIGID;
            //x_env.kind = RIGID;


            //fprintf(stderr, "env after (%zu, >:):\n", i);
            //jl_(result.condition.required);
            //fprintf(stderr, "\n\n");

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
        fprintf(stderr, "ALERT: Verification needed for choice-tree\n");
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
