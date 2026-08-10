# Interfaces and piracy: design status

This note is a compact decision ledger and implementation roadmap for the
interfaces/type-piracy project. It records the cross-cutting conclusions which
are otherwise spread across the implementation and the more detailed
[`INFERENCE_MATCHES_DESIGN.md`](INFERENCE_MATCHES_DESIGN.md) and
[`PACKAGE_GRAPH_DESIGN.md`](PACKAGE_GRAPH_DESIGN.md) notes.

The terms **implemented**, **planned**, and **follow-up** are intentional. Some
semantic query machinery already exists without yet being used by ordinary
caller inference, while other sections specify the constraints that later work
must preserve.

## Core semantic separation

The design keeps four different facts separate:

1. the realized package **requires graph** `≤R`;
2. the explicit implementation rights assigned to a package transaction;
3. whether a callable region is closed to future implementation;
4. the Method and interface-table facts observed by a particular inference
   query.

`≤R` is the transitive closure of attributed `require`, `using`, and `import`
edges between loaded package instances. It is not the set of loaded images and
not the Project/Manifest dependency graph. The declared dependency relation
`≤D` bounds possible requirements but does not imply that a dependency was
loaded or visible. `Precompilation.direct_deps` is only a scheduling
approximation for packages and extensions.

Implementation rights are positive formulas built from unions of formal
package intersections. They are not inferred from `≤R` reachability and are not
canonicalized through it. An ordinary package `P` receives `P`; an extension
`E` of `P` triggered by `A` and `B` receives:

```text
E ∪ (P & A & B)
```

Consequently `P & A & B` remains distinct from `P` even when the current
requires graph makes the intersection operationally degenerate.

## Requires graph and package transactions

**Implemented.** A `LoadedPackageNode` names a loaded root-module instance. All
submodules share that node and its outgoing requirements. The root module owns
serialized direct adjacency; reachability is computed by the compiler.
`Base.PkgId` remains the declared identity key, but node equality is exact
loaded-instance identity.

Root modules record a monotonic `finalized` fact. During incremental output,
only an unfinalized root in the current output transaction may gain a novel
outgoing requires edge. A finalized or restored dependency is closed to new
requires edges, including while its `__init__` runs during downstream
precompilation. Outside incremental output all modules reopen, including at
final application runtime. Repeating an existing edge is always idempotent.

The module-initializer worklists help identify the active output transaction,
but they are not the graph. Openness is canonicalized through the root so that
submodule and root behavior cannot diverge.

The currently direct consumers of graph state are deliberately narrow:

- the incremental-inference first-argument closure gate queries whether the
  package-owner factors are closed nodes;
- later cross-package `≺:` must respect requires reachability; and
- `moduletype` may eventually use `≤R` only for an optional canonicalization
  pass, not for its underlying nodes or union/intersection computation.

Definition-time type- and implementation-piracy admission uses the explicitly
granted rights, not `≤R` reachability.

## Extension rights and future image regions

**Implemented in policy input, incomplete in cache/image handling.** Extension
parent and trigger metadata supplies the formal intersection right. Derived
extension scheduling edges are deps-like facts and must never grant ownership.
The rights belong to the source/precompile definition transaction; loading a
pkgimage validates the context in which declarations were classified rather
than granting rights for the first time.

Extensions remain ordinary simple nodes in `≤R`. Triggering two extensions on
the same packages does not give either extension visibility of or ordering over
the other. Explicit ordinary requires edges remain necessary.

The image layer is separate. Several packages/extensions can be degenerate at
one formal intersection and therefore require a genuinely combined region
image to give compilation a consistent view of every Method definition in
that region. Compiling separate images and assembling them later would reopen
avoidable invalidation gaps. The planned scheduler should:

1. prepare declared dependencies first;
2. advance a frontier over packages whose realized `≤R` facts are known;
3. let a package's current region dynamically grow to absorb newly discovered
   degenerate extensions; and
4. compile an extension normally only when no prior region absorbed it.

This region grouping is a follow-up. The present implementation intentionally
trades the gap for ordinary invalidation rather than degrading inference in
all extensions. Cache keys must eventually include normalized ownership rights,
extension activation inputs, and the region composition, since rights can
change method classification even when the same packages are loaded.

## `packagetype` and productive support

**Implemented as the first conservative analysis.** `packagetype(T)` computes
lower and upper positive package formulas for productive closed subtypes of
`T`. Type piracy concerns the complete method signature uniformly, including
the callable: owning `foo` makes `foo(::Any)` non-piratical, while owning
`typeof(foo)` likewise matters when that value appears in another signature.
The separate first-argument owner is only an implementation-policy concept.

Productivity is semantic: a type is useful to this quantification only when it
admits a closed subtype whose representation is not forced through fundamental
bottom forms such as `Union{}` or `Tuple{}`. This must account for nominal
supertypes; a nominal type whose supertype fixes a degenerate parameter cannot
be rescued merely by its own surface syntax.

The induction handles unions arm by arm, so a degenerate arm does not poison a
productive sibling such as:

```julia
Union{Pair{Union{}, Foo}, Vector{Foo}}
```

Unknown productivity is propagated where required: treating an unknown
nonproductive branch as exact bottom could incorrectly strengthen a package
formula. Type variables follow their bounds recursively. Non-Type parameters
delegate to the package type of `typeof(value)`. For a variable-length Vararg,
the analysis may quantify over productive lengths `N ≥ 1`; a fixed productive
tuple prefix lets an optional tail be ignored.

Union-arm formulas may be met only after proving that type normalization cannot
silently remove an arm by subsumption. The first implementation proves useful
orthogonality/subsumption cases, including nested invariant parameters, and
otherwise joins conservatively. More precise overlapping-arm reasoning and
dependent lower/upper-bound families remain follow-ups.

## Definition-time enforcement

**Implemented.** Before publishing a Method or interface Method, policy checks
run under `jl_method_def_lock`, which serializes classification with both
method-table insertions. Package evaluation can define methods concurrently;
the complete policy snapshot therefore cannot be checked outside this lock.
Loading may update stored rights while holding `require_lock` and then the
definition lock; classification never acquires the loading lock in the reverse
order. Diagnostics are emitted after publication synchronization is released.

The user policy is:

```text
--piracy=warn     default; diagnose and publish
--piracy=strict   diagnose and reject before publication
--piracy=off      publish silently
```

Type-piracy admission asks whether the upper `packagetype(signature)` formula
is within a right granted to the defining package transaction.

Implementation-piracy admission is separate. For an externally closed
first-argument owner, the candidate must be a subtype of a covering interface.
If it is `≺:` an existing Method from another package root, a covering
interface must also be `≺:` that Method. Existing Methods from the same root as
the definition do not consume local interface permission. This permits a
package to define both broad and narrow implementations under one upstream
interface.

Ambiguity between independent sibling implementations is intentional. For
example, implementations `foo(::Bar, ::Any)` and `foo(::Any, ::Baz)` may be
separately valid and become ambiguous only in a downstream `A & B` world. That
intersection cannot be observed at either definition site, and definition
admission does not try to impose a global sibling order.

The first implementation still uses the unrestricted existing `≺:` relation.
Cross-package specificity must eventually be restricted by the requires graph;
until that change, the desired no-invalidation theorem is only conditional.

## TypeName dispatch closure

**Implemented.** `jl_typename_t.dispatch_closed_in` records the root module
which closes dispatch for a TypeName. A new TypeName inherits a non-`nothing`
value from its supertype; otherwise it starts with its defining module's root.
Package finalization scans the root and its submodules' new TypeNames and can
set the value to `nothing` according to definitions made by that package.
Finalization is distinct from serialization so that multiple packages may
eventually share one output image.

Some native TypeNames forward dispatch ownership rather than closing it. In
particular `Any`, `Function`, and Type-containing callable families are marked
as forwarding; `Function` is initialized directly to avoid an expensive scan
of ordinary generic-function methods. Subtypes can still establish/inherit a
concrete package closure.

`arg0_package_owner(T)` reads this closure and forms a positive package formula.
`nothing` maps to top, `Union{}` to bottom, and union arms are joined.
Constructor-like `Type{T}` uses the directly named TypeName owner rather than
charging nominal supertypes. Neither operation canonicalizes through `≤R`.

## Callee-side interface contracts

**Implemented.** Interface assertions for CodeInstances are all-or-nothing.
This is a correctness consequence of current invalidation: interface insertion
can distinguish only whether a CI embeds the complete applicable contract set,
not which subset or return region it used.

The compiler chooses the mode before consuming any interface fact:

- a CI with an empty, completely queried interface set can be marked enforced
  without an IR transformation;
- a dispatchtuple CI may enforce all fully covering interfaces whose return
  templates instantiate to closed static types;
- an abstract/non-dispatchtuple CI covered by any interface remains entirely
  interface-unaware; and
- if the optimizer cannot insert all assertions, the CI remains entirely
  interface-unaware.

An unenforced CI may contain no interface-derived return, exception, effect, or
IR fact. Enforcing CIs narrow their inferred return, add `ReturnTypeError` when
needed, and materialize assertions during inlining/optimization. Redundant
contracts whose return bound is weaker than another are removed. Dynamic
return expressions are deliberately not executed inside the callee for this
first pass: an undefined static parameter leaves the CI unenforced, and generic
dispatch performs the contextual error at the interface site.

The enforcement bit participates in CI equivalence in inference, JIT, and AOT
selection. Interface insertion/removal invalidates intersecting enforcing CIs.
Uncached/constant-propagated results use the terminal edge-only CI cache
partition established separately, so dependencies survive without making
those CIs eligible for ordinary lookup or invocation.

## Semantic call lookup

**Implemented as a query layer; not yet the ordinary inference call resolver.**
The runtime exposes complete raw Method and interface intersections and returns
`Core.InterfaceMatch` values. Cross-table interference preserves the direction
of raw `≺:` rather than collapsing the pair to a symmetric "opens" fact.

`resolve_call_extensibility` computes a conservative positive upper bound on
the open future region without constructing complements. Pointwise, interfaces
open a call exactly when every applicable raw Method is defeated by at least
one applicable interface. Different interfaces may discharge different Method
obligations. Raw Methods are never discarded merely because current dispatch
dominates them; `≺:` is not transitive enough to transfer their closure role.

The positive fixed point tracks resolved Methods, resolved interfaces, and
known-open interfaces. Blocker/opener set comparisons resolve candidates;
query-local `spec_types` regions provide positive coverage. Interfaces are
ordered narrowest first to choose useful necessary seeds. `fully_covers` and
the dual fully-open case improve precision in exact common cases. Returned open
regions conservatively contain every actual future dispatch region, and any
real callee completely covered by their union is removed.

The complete result is split by semantic role:

```text
InferenceLookupResult
    matches       current real callees safe to explore
    future        AnyFutureMethodMatch positive regions
    interfaces    all applicable piecewise contracts
    valid_worlds  intersection of contributing query validity
    fullmatch     coverage by current Methods before future filtering
    unordered     current ambiguity or any future target
```

Keeping `matches` and `future` separate preserves the distinction between
invoking a specific Method and exploring a possibly specialized dispatch table.
`InterfaceMatch` contains its raw MethodMatch plus the instantiated/narrowed
return type. `AnyFutureMethodMatch` does not pretend a Method exists.

During incremental output the first-argument owner gate requires every owner
portion to be either entirely closed in the realized package graph or within
the current package transaction's rights. If any portion fails, the result is
one whole-call future match, no real callees, and the applicable interfaces.
At ordinary runtime this gate is bypassed: all package graph nodes are treated
as closed for inference and ordinary world invalidation remains authoritative.

Any result containing present ambiguity or a future Method is `unordered`.
This deliberately disables ordering-dependent optimizer transformations for
the first implementation. Inference can still explore every real match and use
interface return bounds; it must not lower the result to an `isa`/`:invoke`
chain whose correctness depends on a delicate ordering of ambiguity barriers
or arbitrarily specific future Methods.

## Planned caller-inference behavior

Ordinary abstract-call inference still needs to consume
`InferenceLookupResult`. The intended policy is:

- explore every real `matches` callee on its `MethodMatch.spec_types`;
- do not explore a nonexistent callee for `future`; instead bound its return by
  the applicable interfaces (with `Any` when no useful contract applies);
- retain `MethodError` when current `fullmatch` is false;
- keep unordered calls in generic dispatch rather than applying ordered invoke
  chains; and
- represent generic-call assertions in caller `CallInfo` when the selected CI
  does not have the callee-enforced bit.

Inference may sometimes choose to rely on an interface contract rather than
infer a real callee. The raw `interfaces` list is therefore preserved and the
consumer, not lookup, decides whether a selected invokeable CI already enforces
the contract. `AnyFutureMethodMatch` may cache a return bound as a convenience,
but this must not replace the complete interface list or imply that a future
Method itself owns the contract.

Dispatchtuple calls should eventually have a fast path: once exact dispatch and
all applicable static contracts are proved, they may resolve directly to a
Method or MethodError and use the callee-enforced CI. Abstract calls remain
dynamic whenever an interface or ambiguity can affect dispatch.

Overlay method-table semantics, interaction with union splitting and
`max_methods`, and supplying current transaction rights to every inference
entry point remain explicit decisions before enabling the query globally.

## One semantic inference edge

**Agreed design; not implemented.** The lookup should be tracked as one logical
query edge rather than independent edge kinds for current Methods, missing
Methods, ambiguity, interfaces, and ownership. Define:

```text
Q(atype, context, world) = normalize(inference_matches(...))
```

Revalidation reruns `Q` and invalidates only when its normalized semantic
payload changes. That payload includes:

- current Method identities and query-local `spec_types`;
- the division between real and future regions;
- applicable interfaces and their effective return contracts;
- `fullmatch` and `unordered`; and
- the owner/rights outcome which selected the result.

It excludes container identity, incidental ordering in an unordered result,
and the validity interval itself. One logical edge may be indexed physically in
both Method and interface tables so that either kind of insertion finds it.
This is still one combined semantic dependency, not separate facts whose
validity can drift apart.

The classic negative/full-match edge is a special case. A nonempty future list
needs a watcher even when current Methods fully cover the query: a newly legal
local implementation can replace a future region with a real callee. The old
inference may remain sound under the interface bound, but eager revalidation is
desirable because direct callee inference can become more precise. This gives a
simple general principle: invalidate when the normalized
`InferenceLookupResult` changes, not merely when old machine code becomes
incorrect.

The expected stability theorem is conditional on type- and implementation-
piracy enforcement and requires-respecting specificity. A downstream package
cannot completely dominate an expressible upstream future region without
owning the required types/authority; legal future locations were already
represented by `AnyFutureMethodMatch`. New interfaces can still change the
query result and must be watched. Extension intersection rights and activation
are inputs to the theorem and therefore to cache revalidation.

A practical first version may invalidate live queries conservatively and use
exact semantic comparison when restoring pkgimages. Red/green comparison,
batching, and more selective indexing are performance refinements; they must
not fragment the logical result into independently valid pieces.

## Prospective `@nospecialize` interface masks

**Deferred optimization.** An interface may eventually use
`@nospecialize` on a non-callable argument to remove that coordinate from both
the ownership contribution and the concreteness required for a static invoke.
This addresses interfaces such as `foo(self::Any, item::Any)` whose
implementations conventionally leave `item` unspecialized.

With overlapping interfaces, implementation admission is existential: any one
applicable interface mask may license a Method. Inference is the dual and must
consider the union of implementation families licensed by every applicable
mask, while return contracts remain conjunctive. Equal-signature interface
definitions replace one another in a world rather than contributing two masks.

There is no generally sound single effective mask. If one interface retains
factor `A`, another retains `B`, and a package owns only `A & B`, combining the
masks can invent authority supplied by neither interface. Treating the overlap
as entirely unmasked is a sound inference over-approximation, but loses
precision. Exact inference must retain the disjunction of per-interface
authority alternatives. The detailed algebra is recorded in
`INFERENCE_MATCHES_DESIGN.md`.

## Remaining sequence

The intended order for follow-on work is:

1. wire `InferenceLookupResult` into abstract-call inference and optimizer
   policy while preserving existing callee enforcement;
2. add the combined semantic query edge and revalidation path;
3. restrict cross-package `≺:` according to the requires graph and revisit
   ambiguity edges as part of the same change;
4. complete extension-right/cache validation and region-image grouping; and
5. consider masked `@nospecialize` authority as a codegen/invokeability
   optimization after the unmasked semantics are stable.

The design intentionally favors representative final inference quality plus
ordinary invalidation over defensive despecialization introduced solely by an
interim cache or image implementation.
