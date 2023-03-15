#include <string.h>
#ifdef _OS_WINDOWS_
#include <malloc.h>
#endif
#include "julia.h"
#include "julia_internal.h"
#include "julia_assert.h"

#ifdef __cplusplus
extern "C" {
#endif


// This list fills me with determination.

/**
 * List of types:
 *  [x] Any
 *  [x] Union
 *      [x] Union{ }
 *      [x] Union{ ... }
 *  [ ] Kinds
 *      [ ] typeof(Union{ })
 *      [ ] typeof(Union{...})
 *      [ ] UnionAll
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
 *  [ ] TypeVars
 *      [ ] Statically diagonal
 *      [ ] Statically non-diagonal
 *      [ ] Dynamically diagonal
 *  [ ] Type{T} ?
 *
 **/

/**
 * Our handling of typevars looks like this:
 *   1. Add them to our environment
 **/

// TODO: Later, we'll get the environment back out...

typedef enum {
    RIGID,
    FLEXIBLE,
} jl_varkind_t;

typedef struct jl_varbinding_t {
    jl_tvar_t *var;
    //jl_value_t *lb;
    //jl_value_t *ub;
    jl_varkind_t kind; // \forall vs. exists
    int16_t inv_depth;

    // TODO: innervars?
    struct jl_varbinding_t *prev;
} jl_varbinding_t;

/**
 * TODO: I'd like to think carefully about how I'd solve this problem
 *       without multiple occurrences of RHS variables.
 *
 *  In that case, we only ever have to compare against
 *  "pre-existing" bounds.
 **/

typedef struct {
    jl_varbinding_t *vars;
    int16_t inv_depth;
} jl_stenv_t;

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

// TODO: Start adding some op variants:
//   - Also what does a primitive intersection type look like?
//
//   - shuttle_subtype: <=>, disjoint, incomparable
//      - depending on which one we want, we might
//        be able to be more efficient.
//      - For now, only consider the needs of subtyping
//   - intersection
// some op-variants (intersection, etc.)
JL_DLLEXPORT int jl_simple_subtype_env(jl_value_t *x, jl_value_t *y, jl_varkind_t x_kind, jl_varkind_t y_kind, jl_stenv_t *env) {
    //fprintf(stderr, "subtyping simply for (equal: %d):\n", x == y);
    //jl_(x);
    //jl_(y);
    if ((x == y) || (x == (jl_value_t*)jl_bottom_type) || (y == (jl_value_t*)jl_any_type))
        return 1;

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
    if (jl_typeis(x, jl_tvar_type) || jl_typeis(y, jl_tvar_type)) {
        int8_t R = !jl_typeis(x, jl_tvar_type);
        jl_tvar_t *tv = (jl_tvar_t *)(R ? y : x);
        jl_varbinding_t *vb = env->vars;
        while (vb != NULL) {
            if (vb->var == tv)
                break;
            vb = vb->prev;
        }

        jl_varkind_t kind = vb ? vb->kind : (R ? y_kind : x_kind);
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
            if (R) {
                if (vb->inv_depth == env->inv_depth)
                    return 1;

                return jl_simple_subtype_env(x, tv->lb, x_kind, y_kind, env);
            } else {
                return jl_simple_subtype_env(tv->ub, y, x_kind, y_kind, env);
            }
        } else if (kind == FLEXIBLE) {
            /**
             * Check against existing bounds
             **/
            if (R) {
                // Y always FLEXIBLE here
                if (!jl_simple_subtype_env(x, tv->ub, x_kind, y_kind, env))
                    return 0;

                /**
                 * I need to accumulate the bound I've discovered and stick it into the AND/OR tree
                 **/

                /**
                 * We just checked that x <: UB
                 *
                 * Now, we need to make sure that Z <: x.
                 * We do this by adding x as a LB.
                 **/
                return 1; // 1 *with a condition* in reality
            } else {
                if (vb->inv_depth == env->inv_depth)
                    return 1;

                // X always FLEXIBLE here
                if (!jl_simple_subtype_env(tv->lb, y, x_kind, y_kind, env))
                    return 0;

                return 1; // 1 *with a condition* in reality
            }
        }
    }

    // TODO: Watch out, this catches type-vars too...
    if (!jl_is_type(x) && !jl_is_type(y)) {
        return jl_egal(x, y);
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

    /**
     * We can either provide custom order that flips and constant rigidity
     * OR we can flip rigidity and provide custom order
     **/
    if ((jl_is_unionall(x) || jl_is_unionall(y))) {
        // This can happen when we allow a RHS UnionAll that
        // actually appears nowhere
        int8_t R = !jl_is_unionall(x);
        jl_unionall_t *uax = (jl_unionall_t *)(R ? y : x);

        jl_varbinding_t *prev_vb = env->vars;
        jl_varbinding_t vb = { uax->var, R ? y_kind : x_kind, env->inv_depth, env->vars };

        env->vars = &vb;
        int result;
        if (R) {
            result = jl_simple_subtype_env(x, uax->body, x_kind, y_kind, env);
        } else {
            result = jl_simple_subtype_env(uax->body, y, x_kind, y_kind, env);
        }
        env->vars = prev_vb;

        return result;
    }

    /**
     * Might be worth flipping order so that this is simpler:
     * (OR just factoring these logic out to separate functions)
     **/

    // This is our "forall-exists" loop here
    if (jl_is_uniontype(x)) {
        jl_uniontype_t *ux = (jl_uniontype_t *)x;

        return jl_simple_subtype_env(ux->a, y, x_kind, y_kind, env) &&
            jl_simple_subtype_env(ux->b, y, x_kind, y_kind, env);
    } else if (jl_is_uniontype(y)) {
        jl_uniontype_t *uy = (jl_uniontype_t *)y;

        return jl_simple_subtype_env(x, uy->a, x_kind, y_kind, env) ||
            jl_simple_subtype_env(x, uy->b, x_kind, y_kind, env);
    }

    /**
     * Now I just need to handle unions, distributivity and everything else...
     *
     * Quite an ambitious order for today!
     *   But I believe in us =)
     **/

    /**
     * Okay, how do we handle invariant constructors, now?
     * We can either request equality or check both directions
     **/

    if (jl_is_datatype(x) && jl_is_datatype(y)) {
        // Handle datatypes with no parameters
        jl_datatype_t *dx = (jl_datatype_t *)x;
        jl_datatype_t *dy = (jl_datatype_t *)y;
        while (dx->name != dy->name) {
            if (dx == jl_any_type)
                return 0;
            dx = dx->super;
        }

        size_t np_x = jl_nparams(dx);
        size_t np_y = jl_nparams(dy);

        if (np_x != np_y)
            return 0;

        if (!jl_is_tuple_type(dx))
            env->inv_depth += 1;

        int result = 1;
        for (size_t i=0; i < np_x; i++) {
            jl_value_t *xi = jl_tparam(dx, i);
            jl_value_t *yi = jl_tparam(dy, i);
            if (!jl_simple_subtype_env(xi, yi, x_kind, y_kind, env)) {
                result = 0;
                break;
            }

            // We might want to go ahead and switch
            // to forall_equals here
            if (!jl_is_tuple_type(dx) && !jl_simple_subtype_env(yi, xi, y_kind, x_kind, env)) {
                result = 0;
                break;
            }

            // TODO: forall_exists_equal is an optimization the main
            //       algorithm has (i.e. equality)
            //  -> it has a component-wise comparison fast-path
        }

        if (!jl_is_tuple_type(dx))
            env->inv_depth -= 1;
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
    return 0;
}

JL_DLLEXPORT int jl_simple_subtype(jl_value_t *x, jl_value_t *y) {
    jl_stenv_t env = { NULL, 0 };
    /*jl_(x);*/
    /*jl_(y);*/
    return jl_simple_subtype_env(x, y, RIGID, FLEXIBLE, &env);
}


#ifdef __cplusplus
}
#endif
