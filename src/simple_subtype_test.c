#include <stdbool.h>
#include <malloc.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>

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

enum and_or : uint8_t { AND, OR };

// And then the AND/OR structure:
struct jl_agg_result_t {
    uint16_t size;
    uint16_t total_size; // Total number of "bits" in a distributive tuple

    enum and_or type;
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
    /*jl_varbinding_t *env;*/
    /*jl_value_t *bound;*/
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

typedef struct {
    char *buffer;
    size_t sz;
    size_t capacity;
} jl_linear_alloc_t;

static inline size_t align_forward(size_t addr, size_t align) {
    return (addr + (align - 1)) & ~(align - 1);
}

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
    bool complement_seen;
    bool mask_seen;
} complement_result_t;

//enum {
    //CLEAR_MASK,
    //CLEAR_COMPLEMENT,
    //V


/**
 * I kind of want to get rid of 
 **/
struct complement_state {
    jl_agg_result_t *tree;
    uint32_t bit_offset;
    uint16_t component;
    bool cleared;

    struct complement_state *subqueue;
    struct complement_state *next;
    //struct complement_state *sub_state; // null-terminated
};

/**
 * We need the RHS only to tell us where any sub-tree we haven't discovered yet are,
 * which we indeed need.
 *
 *
 * How do we handle allocation?
 *   -> No frees: queue index only increases, except at base level
 *   -> local resizing: we can shrink our own queue and re-use items
 *   -> proper up-front allocation:
 *      -> we scan *all* dimensions and get the maximum queue depth
 **/


/**
 * A. Setup-only, then actual cartesian computation
 * B. Setup + computation, then separate tail call
 * C. Combined function
 **/

void zero_root_bits(uint64_t *bvec, size_t offset, jl_agg_result_t *tree)
{
    size_t bit_index = offset;
    size_t boundary = offset;
    for (size_t b = 0; b < tree->size; b++) {
        // Leave any sub-trees unmodified
        jl_agg_result_t *subtree = unwrap_aggregate(tree->results[b]);
        if (subtree && subtree->is_distributive_tuple && !subtree->is_distributive_tuple_root) {
            setbits(bvec, boundary, bit_index, false);
            bit_index += subtree->total_size - 1;
            boundary = bit_index;
        } else bit_index += 1;
    }
    setbits(bvec, boundary, bit_index, false);
}

/**
 * I'm starting to think this complement function is going to be a major
 * hub for our new algorithm, so it's probably for the best that it's
 * been given some extra tools.
 *
 * The overall structure is going to look like:
 *   - AND / OR / TUPLE resolver (tuple by far the most complicated)
 *   - A top-level bounds-forcing-solver
 *   - recursion to handle recursive bounds, etc.
 **/

/**
 * This function looks complicated, but it's just calculating complements!
 *
 * N.B. This function uses a somewhat-complicated queue mechanism in order to generate
 *      the minimal number of cartesian components required to cover the complement of
 *      the provided `mask`. This provides exponential speed-up when performing sub-
 *      typing on distributive tuples.
 **/

/**
 * Generate the next Cartesian complement for the provided bit-vector.
 *
 * Returns false if all complements have been exhausted.
 **/
bool take_complement(uint64_t *bvec, uint64_t *mask, struct complement_state *state, jl_linear_alloc_t *alloc);

/**
 * Private methods
 **/
bool take_nested_complement(uint64_t *bvec, uint64_t *mask, struct complement_state *state, jl_linear_alloc_t *alloc);
bool take_dimension_complement(uint64_t *bvec, uint64_t *mask, struct complement_state *state, jl_linear_alloc_t *alloc);

bool take_dimension_complement(uint64_t *bvec, uint64_t *mask, struct complement_state *state, jl_linear_alloc_t *alloc)
{
    jl_agg_result_t *tree = unwrap_aggregate(state->tree->results[0]);
    jl_agg_result_t *component = unwrap_aggregate(tree->results[state->component]);

    // TODO: Maybe move this here
    //if (!(component && component->is_distributive_tuple && !component->is_distributive_tuple_root))
        //return false;

    jl_small_result_t *item = &component->results[0];
    const jl_small_result_t *end = &component->results[component->size];

    //fprintf(stderr, "component: %d size: %d\n", state->component, component->size);
    bool complement_taken = false;
    uint32_t bit_index = state->bit_offset;
    while (item < end) {
        jl_agg_result_t *subtree = unwrap_aggregate(*item++);
        if (subtree && subtree->is_distributive_tuple && !subtree->is_distributive_tuple_root) {
            //fprintf(stderr, "recursing... (bit_index = %d)\n", bit_index);

            // Enqueue a sub-tree to generate all complements for nested tuples
            struct complement_state *tail = state->subqueue;
            state->subqueue = (struct complement_state *)linear_alloc(sizeof(struct complement_state),
                                        alignof(struct complement_state), alloc);
            *(state->subqueue) = (struct complement_state) {
                /* tree */ subtree, /* bit_offset */ bit_index, /* component */ UINT16_MAX,
                /* cleared */ false, /* subqueue */ NULL, /* next */ tail
            };
            if (take_complement(bvec, mask, state->subqueue, alloc))
                complement_taken = true;
            //fprintf(stderr, "(done)");

            bit_index += subtree->total_size;
        } else {
            //fprintf(stderr, "bit_index: %d\n", bit_index);
            // Otherwise, all we have to do is set any mask bits to zero
            if (getbit(mask, bit_index))
                setbit(bvec, bit_index, false);
            else if (getbit(bvec, bit_index))
                complement_taken = true;

            bit_index += 1;
        }
    }
    return complement_taken;
}

bool take_nested_complement(uint64_t *bvec, uint64_t *mask, struct complement_state *state, jl_linear_alloc_t *alloc)
{
    jl_agg_result_t *tree = unwrap_aggregate(state->tree->results[0]);
    jl_agg_result_t *component = unwrap_aggregate(tree->results[state->component]);

    bool complement_taken = false;
    struct complement_state *queue = state->subqueue;
    while (queue != NULL) {
        if (take_complement(bvec, mask, queue, alloc))
            complement_taken = true;
        queue = state->next;
    }
    if (complement_taken && !state->cleared) {
        zero_root_bits(bvec, state->bit_offset, component);
        state->cleared = true;
    }
    return complement_taken;
}

bool take_complement(uint64_t *bvec, uint64_t *mask, struct complement_state *state, jl_linear_alloc_t *alloc)
{
    jl_agg_result_t *tree = unwrap_aggregate(state->tree->results[0]);
    assert(tree);

    if (state->component != UINT16_MAX) {
        // If any sub-tree took a complement, then return without moving onto the next component
        if (take_nested_complement(bvec, mask, state, alloc))
            return true;

        // Restore the previous dimension
        //fprintf(stderr, "restoring from %d to %d\n", state->bit_offset, state->bit_offset + component->total_size);
        jl_agg_result_t *component = unwrap_aggregate(tree->results[state->component]);
        copybits(bvec, mask, state->bit_offset, state->bit_offset + component->total_size);
        state->bit_offset += component->total_size;
    }
    //fprintf(stderr, "advancing\n");

    // Advance to the next (incomplete) dimension
    while (true) {
        state->subqueue = NULL;
        state->component += 1;
        if (state->component == tree->size)
            return false; // done

        jl_agg_result_t *component = unwrap_aggregate(tree->results[state->component]);
        if (!(component && component->is_distributive_tuple && !component->is_distributive_tuple_root))
            continue; // non-distributive dimension

        // The actual work: Take a complement in this dimension and enqueue
        // any nested tuples that might need further iterations.
        if (take_dimension_complement(bvec, mask, state, alloc))
            return true;

        // Oops, the complement we took is empty. Restore the bits and move on to the next component.
        copybits(bvec, mask, state->bit_offset, state->bit_offset + component->total_size);
        state->bit_offset += component->total_size;
    }
}

/**
 * Depending on how our analysis works out tomorrow, we'll either:
 *   A. Branch and generate a number of possible enable-bit solutions for the distributivity problem
 *       -> Each one will require forcing bit-by-bit
 *       -> Is it permitted to lock our tuple-enablement bits? I don't think so...
 *          We didn't branch on bits that might conflict with these forced-bits,
 *          even if they have good alternatives.
 *   B. Eagerly apply bounds during the tuple solve (where we still branch on each enable-bit-add)
 *       -> Similar awkwardness with the forced-bits that I need to think about carefully
 *
 *  After thinking about how to do forcing, it should become obvious which of these is
 *  the right approach.
 **/

void printBits(size_t const size, void const * const ptr)
{
    unsigned char *b = (unsigned char*) ptr;
    unsigned char byte;
    int i, j;
    
    for (i = size-1; i >= 0; i--) {
        printf("'");
        for (j = 7; j >= 0; j--) {
            byte = (b[i] >> j) & 1;
            printf("%u", byte);
        }
    }
    puts("");
}

jl_agg_result_t *create_tuple(size_t n_comp, size_t bits_per_comp, jl_linear_alloc_t *alloc) {
    const size_t K = bits_per_comp;
    const size_t N = n_comp;

    jl_agg_result_t *outer_and = (jl_agg_result_t*)linear_alloc(
            sizeof(jl_agg_result_t) + N * sizeof(jl_small_result_t),
            alignof(jl_agg_result_t), alloc);
    outer_and->size = N;
    outer_and->total_size = K * N;
    outer_and->type = AND;
    outer_and->is_distributive_tuple = 1;
    outer_and->is_distributive_tuple_root = 0;

    for (int i = 0; i < N; i++) {
	jl_agg_result_t *inner_and = (jl_agg_result_t*)linear_alloc(
                sizeof(jl_agg_result_t) + K * sizeof(jl_small_result_t),
                alignof(jl_agg_result_t), alloc);
	inner_and->size = K;
        inner_and->total_size = K;
	inner_and->type = AND;
        inner_and->is_distributive_tuple = 1;
        inner_and->is_distributive_tuple_root = 0;
        for (int j = 0; j < K; j++)
            inner_and->results[j] = wrap_boolean_result(true, 0);

	outer_and->results[i] = wrap_aggregate_result(inner_and);
    }

    jl_agg_result_t *rhs = (jl_agg_result_t*)linear_alloc(
            sizeof(jl_agg_result_t) + 1 * sizeof(jl_small_result_t),
            alignof(jl_agg_result_t), alloc);

    rhs->size = 1;
    rhs->total_size = K * N;
    rhs->type = OR;
    rhs->is_distributive_tuple = 1;
    rhs->is_distributive_tuple_root = 0;
    rhs->results[0] = wrap_aggregate_result(outer_and);

    return rhs;
}

/**
 * After we have well-tested subtyping & (non-empty) intersection
 *  -> the next stop will be improving the type-map
 *       -> This might mean increasing the splitting, I'm not sure
 *       -> I really want to take some statistics and see how it's all organized
 *
 * It's a bummer, because we're on track to have this change ready in a few more
 * days, but I think I need to focus on other things in the first half of this
 * week at least.
 **/

/**
 * TODO: I should have an integration test that does a read and a write from a
 *       tuple system, and then I should hand-write test cases that verify
 *       the generated complements, etc.
 **/

int main() {
    static const size_t CAPACITY = 4096;
    char *buffer = (char *)malloc(CAPACITY);
    jl_linear_alloc_t alloc;
    linear_alloc_init(buffer, CAPACITY, &alloc);

    static const size_t K = 8;
    static const size_t N = 6;

    jl_agg_result_t *rhs = create_tuple(N, K, &alloc);
    rhs->is_distributive_tuple_root = true;

    {
        jl_agg_result_t* outer_and = unwrap_aggregate(rhs->results[0]);
        jl_agg_result_t* inner_and = unwrap_aggregate(outer_and->results[2]);
        inner_and->results[2] = wrap_aggregate_result(create_tuple(2, 2, &alloc));
        inner_and->size = 5;
    }

    // We *still* need two copies for our solution right now:
    //   (1) to allow us to update the mask and not restore it in the first place
    //   (2) to copy the solution out of the preferred result
    //         (could be fixed by annotating with `volume` instead of using bitmask)
    //            but then we lose `copybits`
    
    uint64_t bvec = 0b11111111'11111111'11111111'11111111'11000111'11111111;
    uint64_t mask = 0b11111110'11110001'11111111'10101010'11000111'11000011;
    size_t bit_offset = 0;
    fprintf(stderr, "input:       ");
    printBits(6, &bvec);
    fprintf(stderr, "\n");
    fprintf(stderr, "mask:        ");
    printBits(6, &mask);
    fprintf(stderr, "\n");

    struct complement_state *queue = (struct complement_state *)linear_alloc(sizeof(struct complement_state),
                                                  alignof(struct complement_state), &alloc);
    *queue = (struct complement_state) {
        /* tree */ rhs, /* bit_offset */ 0, /* component */ UINT16_MAX,
        /* cleared */ false, /* subqueue */ NULL, /* next */ NULL
    };
    //size_t i = 0;
    while (take_complement(&bvec, &mask, queue, &alloc)) {
        fprintf(stderr, "complement:  ");
        printBits(6, &bvec);
        fprintf(stderr, "\n");
	bit_offset = 0;
        //if (i++ == 2)
        //break;
    }

    // So, I managed to re-cover the solution without any copies actually
    /*bool take_nth_cartesian_complement(size_t n, uint64_t *bvec, uint64_t *mask, jl_agg_result_t *rhs, size_t *bit_offset)*/

}
