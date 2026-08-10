# Inference Matches and Interface Openness

This note records the pointwise semantics of interface openness and the
high-level structure of the inference lookup that combines Methods and
interfaces. It also records the conservative positive fixed point used when
Julia cannot represent the required type differences directly.

## First-argument package-owner gate

Inference does not enumerate hypothetical future implementation authorities.
Instead it first asks whether dispatch ownership for the complete callable
first-argument region is stable in the current compilation context.

`arg0_package_owner(arg0(atype))` returns a positive DNF package formula. During
incremental output, every portion of that formula must satisfy one of two
conditions:

```text
closed = every factor is a closed node in the realized package graph
self   = the portion implies one of the current transaction's ownership rights
```

Every portion must be closed or self. Bottom has no portions and is harmless.
Top has one empty portion, which is neither closed by graph nodes nor normally
self-owned, so an open `dispatch_closed_in === nothing` fails the gate.

The check is deliberately all-or-nothing. A union owner such as `P ∪ Q` is
stable only when both alternatives are closed/self. The lookup does not try to
recover the type-region partition erased by `arg0_package_owner`. If any portion
fails, inference returns no real callees and one
`AnyFutureMethodMatch(atype)`. Applicable interfaces are still returned so
their cumulative return contracts remain available.

Ordinary runtime bypasses this gate. Although modules are open to permanent
effects there, ordinary world-age backedges and invalidation protect the
current lookup. Graph closure and self rights are consulted only while
generating incremental output.

## Pointwise implementation policy

After the first-argument package-owner gate succeeds, fix a concrete call type
`ϵ`. Let:

```text
Pϵ = all Methods applicable at ϵ
Nϵ = all interfaces applicable at ϵ
```

The direct policy relation is:

```text
I ≺: M     ⇒ interface I defeats and opens Method M
I ≺/: M    ⇒ Method M wins and remains closed against I
```

In particular, an equal-signature interface does not open a Method. The
interface must be strictly more specific according to the implementation-policy
specificity relation.

The call type is interface-open precisely when at least one interface applies
and every applicable Method is defeated by at least one interface:

```text
open(ϵ) ⇔ Nϵ ≠ ∅ and ∀M ∈ Pϵ, ∃I ∈ Nϵ such that I ≺: M
```

Equivalently, it is closed when some Method is undefeated:

```text
closed(ϵ) ⇔ Nϵ = ∅ or ∃M ∈ Pϵ, ∀I ∈ Nϵ, I ≺/: M
```

Thus the applicable interfaces must form a directed dominating set for the
applicable Methods in the bipartite interface/Method policy graph.

Each raw Method is an independent closure contributor. A Method is not removed
from this policy calculation merely because another Method currently dominates
it for dispatch. This prevents unsafe dominance transfer through
non-transitive specificity. For example:

```text
I  ≺: M₂
M₂ ≺: M₁
I  ≺/: M₁
```

Opening `M₂` with `I` does not transfer `M₂`'s dominance over `M₁` to
`I`; `M₁` remains an undefeated closure contributor.

Different interfaces may discharge different Method obligations. Consequently,
if:

```text
I₁ ≺: M₁
I₂ ≺: M₂
R <: I₁ ∩ I₂
```

then `I₁` may open `R` against `M₁` while `I₂` opens it against `M₂`.
No single interface must dominate every Method.

## Boolean form

Let:

```text
rᵢₘ = true  iff  Iᵢ ≺: Mₘ
```

Then pointwise interface openness is the monotone CNF formula, guarded by the
existence of an applicable interface:

```text
open(ϵ) = (Nϵ ≠ ∅) ∧ ⋀ₘ ⋁ᵢ rᵢₘ
```

Each Method contributes one clause saying that at least one interface must open
it. Closedness is the De Morgan dual:

```text
closed(ϵ) = (Nϵ = ∅) ∨ ⋁ₘ ⋀ᵢ ¬rᵢₘ
```

The result is therefore an AND across Methods and an OR across interfaces, not
a total ordering of a combined candidate list.

## Coinductive interpretation

The same policy can be described as a greatest-fixed-point computation.

For a provisionally effective set of interfaces `X ⊆ Nϵ`, define the Methods
which survive them:

```text
Φ(X) = { M ∈ Pϵ │ no I ∈ X satisfies I ≺: M }
```

For a provisionally surviving set of Methods `Y ⊆ Pϵ`, define the interfaces
which survive those Methods:

```text
Ψ(Y) = { I ∈ Nϵ │ ∀M ∈ Y, I ≺: M }
```

Both `Φ` and `Ψ` are order-reversing. Their composition:

```text
T = Ψ ∘ Φ
```

is order-preserving on the finite powerset lattice `𝒫(Nϵ)`. The
Knaster–Tarski theorem therefore supplies a least fixed point `μT` and a greatest
fixed point `νT`. Interface openness chooses the coinductive solution `νT`.
When the recursive solution is unique, `μT = νT`, so the inductive and
coinductive descriptions coincide.

To compute `νT`, begin with every applicable interface provisionally effective:

```text
X₀ = Nϵ
Y₁ = Φ(Nϵ)
X₁ = Ψ(Y₁)
```

The Method-wins-by-default rule makes this converge in one such two-step pass:

```text
Y₁ = ∅  ⇒ X₁ = Nϵ
Y₁ ≠ ∅  ⇒ X₁ = ∅
```

If `Y₁` is empty, every Method is opened and every interface remains
effective. If `Y₁` contains `M`, then no interface in `Nϵ` defeats `M`, so
that Method defeats every interface and `X₁` is empty. Either result is
already a fixed point.

An alternating interface/Method specificity cycle for which every Method has an
interface opener therefore selects the open, mutually supporting solution. This
is the intended coinductive interpretation.

This all-or-nothing result concerns implementation openness at the single call
type `ϵ`. It does not remove interface return contracts. Contract applicability
is independent of whether an interface contributes an open future region.

## Prospective masked interface authority

A future interface-specific meaning for `@nospecialize` may let an interface
exclude marked declared arguments from both type-ownership admission and the
concreteness needed for a static invoke proof. This section records the
authority algebra that such a design must preserve; the current implementation
does not yet attach this policy meaning to `@nospecialize`.

Let `K(I)` be interface `I`'s set of masked argument coordinates, excluding the
callable itself. Let `π[K](S)` be the package-type analysis of signature `S`
with ownership contributions from coordinates in `K` omitted, while preserving
the signature's binders and all dependencies among unmasked coordinates. An
implementation `M` from package `P` may use `I` as its authority witness only
if:

```text
M <: I
π[K(I)](M) ≤ Rights(P)
```

along with the ordinary Method/interface specificity policy. When several
interfaces cover `M`, admission is existential: any one interface may witness
the definition. Inference has the dual obligation. It must consider the union
of the future implementation families licensed by every applicable interface:

```text
Allowed(M, P) ⇔ ∃ applicable I: Licenses(I, M, P)
Future(C)      = ⋃ { Future(I, C) │ I is applicable at C }
```

Consequently a static invoke proof must survive every applicable authority
alternative. Return contracts compose differently: all interfaces applicable
to the call constrain its return, independently of which interface could have
licensed an implementation.

Two interfaces with identical signatures do not provide simultaneous mask
alternatives: ordinary method-table replacement leaves only the latest one in
a given world. Distinct, overlapping signatures can carry incomparable masks.
For equal regions, masking more coordinates is a stricter authority option;
an option which masks fewer coordinates permits every implementation permitted
by the more-masked option and potentially more.

Several mask alternatives cannot in general be collapsed to one effective
mask for definition admission. In particular, suppose one interface projection
retains ownership factor `A`, another retains `B`, and a package owns only the
formal intersection right `A & B`. Neither interface separately witnesses the
definition:

```text
(A ≤ A & B) ∨ (B ≤ A & B) = false
```

An unmasked or combined projection retains both factors and does witness it:

```text
A & B ≤ A & B = true
```

Thus merging the masks can invent an implementation authorized by no actual
interface. Treating their overlap as unmasked is nevertheless a sound
inference over-approximation: it adds hypothetical future implementations and
may lose an optimization, but cannot omit a legal one. Exact inference must
instead retain the disjunction of per-interface authority options. This
non-distributivity is intentional because intersection ownership rights are
not canonicalized or decomposed through the requires relation.

## Lift from points to type regions

Let the interface-covered region be:

```text
N = ⋃ { I │ I is an applicable interface }
```

For every raw intersecting Method `M`, define its interface-open region:

```text
Oₘ = ⋃ { I │ I is applicable and I ≺: M }
```

The portion which remains closed by `M` is:

```text
Cₘ = M ∖ Oₘ
```

After the first-argument owner gate succeeds, the exact interface-open region
is:

```text
Open = N ∖ ⋃ₘ Cₘ
     = N ∩ ⋂ₘ (¬M ∪ Oₘ)
```

The explicit `N` factor prevents a call region with no interface from becoming
vacuously open. Definition-time same-PackageRoot exemptions remain an
enforcement concern; inference over a finalized/current Method table passes all
raw applicable Methods to the computation.

## Positive `resolve_call_extensibility` computation

The runtime records the cross-table specificity relation on both kinds of
Method. For an intersecting ordinary Method `M` and interface `I`:

```text
I in M.interface_interferences  iff  M ≺/: I
M in I.interface_interferences  iff  I ≺/: M
```

The inventories are directional. If `I ≺: M`, only the first membership is
present; if `M ≺: I`, only the second is present; if neither signature wins,
both are present. Disjoint pairs occur in neither inventory. This preserves the
raw cross-table relation rather than merely recording symmetric "opening
pairs".

The relation is extended when either kind of Method is activated. The scan is
performed at the activation world, not the preceding world: pkgimage entries
are activated sequentially at one shared world, so the later member of a
same-image Method/interface pair must be able to observe the earlier member.
The insertion path updates both objects' inventories.

`resolve_call_extensibility` receives:

```text
Callees     = the ordinary dispatch-resolved and ordered Method list
Methods     = every raw applicable Method
Interfaces  = every raw applicable interface
```

All inputs are query-local matches. `Methods` and `Interfaces` must not have
been filtered by ordinary dispatch; `Callees` is the deliberately filtered and
ordered Method result. An interface is represented as:

```text
InterfaceMatch(
    match    = its query-local MethodMatch,
    rettype  = its return contract instantiated in match.sparams,
               or nothing when a required static parameter is undefined)
```

Interface return expressions are currently restricted to type templates
evaluated when the interface is declared. Matching performs only static-
parameter substitution; it never executes interface-provided code in a
callee. An undefined required parameter prevents callee enforcement and is
reported by dynamic dispatch as an `UndefVarError` scoped to the interface
Method.

From the directional inventories, construct:

```text
Openers(M)  = intersecting interfaces I for which I ≺: M
Blockers(I) = intersecting Methods M for which I ≺/: M
```

Sort interfaces narrow-to-broad by strict inclusion of their query-local
`spec_types`. The stable topological sort uses raw traversal order to choose
among candidates that are simultaneously available. This ordering does not
change the inductive resolution; it only chooses the smallest available
conservative seed when a coinductive component has no first step. The runtime
interface-intersection query performs this sort once, before constructing its
`InterfaceMatch` result, so contract processing and the openness fixed point can
share the same ordered matches.

Maintain separate resolved states for Methods and interfaces, the selected
`OpenInterfaces`, and a union of `SettledRegions` (the implementation's `R`).
"Resolved" means that the candidate's whole query-local region has been
accounted for; it does not mean that a Method is closed or that an interface is
open.

Coverage is checked before the dependency conditions. In particular, an
interface whose blockers are resolved must not be added to `OpenInterfaces` if
its region was already settled by a closed Method. Consequently the operations
that mark an uncovered Method closed or an uncovered interface open may settle
their regions without repeating the coverage proof.

```text
repeat:
    for each unresolved Method M:
        if M.spec_types is covered by SettledRegions:
            resolve M
        else if every interface in Openers(M) is resolved:
            resolve M
            settle M.spec_types

    for each unresolved interface I:
        if I.spec_types is covered by SettledRegions:
            resolve I
        else if every Method in Blockers(I) is resolved:
            resolve I
            add I to OpenInterfaces
            settle I.spec_types

    if every interface is resolved:
        return OpenInterfaces

    if neither loop made progress:
        choose the first unresolved interface in narrow-to-broad order
        resolve it coinductively
        add it to OpenInterfaces
        settle its spec_types
```

The progress test is required even though the successful termination condition
mentions only interfaces. An interface resolved late in one pass may make a
Method, and therefore further interfaces, inductively resolvable on the next
pass. A coinductive seed is chosen only after this alternating inductive chain
is exhausted.

A resolved Method may be settled because all portions opened against it have
already been accounted for by its resolved openers; its remainder is closed.
Once every blocker of an interface is resolved, any portion not already
settled is opened by that interface, so selecting the entire interface region
is a conservative positive upper bound.

Coverage is tested against the cached Julia `Union` of settled regions, which
recognizes union coverage without requiring complements or new intersections.
A `fully_covers` Method that becomes settled
accounts for the whole call query. A selected interface whose MethodMatch
`fully_covers` the query analogously `fully_opens` it. Either case terminates
the computation immediately. The API converts the selected interfaces directly
to `AnyFutureMethodMatch` values. No expensive cleanup pass is performed: merely
shrinking the returned list would not shrink its represented open region.

The result guarantees:

```text
the actual open dispatch region ⊆ R(FutureMatches)
```

where `R` is the union of the returned query-local interface regions. A callee
whose whole `spec_types` is covered by this union must be removed from the
fixed-callee list. Raw `InterfaceMatch` values remain in the complete inference
result independently for return-contract processing.

## High-level inference lookup

The lookup keeps current dispatch resolution separate from future
implementation policy:

```text
inference_matches(atype, world, self_rights, limit):
    raw_interfaces := intersect every live interface with atype at world

    if generating incremental output:
        owner := arg0_package_owner(arg0(atype))

        for every portion in owner:
            closed := every factor is a closed realized-package-graph node
            self   := portion is within self_rights

            if neither closed nor self:
                return InferenceLookupResult(
                    matches      = [],
                    interfaces   = raw_interfaces,
                    future       = [AnyFutureMethodMatch(atype)],
                    fullmatch    = false,
                    unordered    = true,
                    valid_worlds = raw interface validity)

    raw_methods := intersect every live Method with atype at world

    current := resolve ordinary dispatch on a copy of raw_methods
               using the existing Method-only sorting, ambiguity, coverage,
               SCC, and limit rules

    matches := current.matches

    interfaces := form InterfaceMatch values from raw_interfaces,
                  including their effective narrowed return contracts

    matches, future := resolve_call_extensibility(
                           matches, raw_methods, interfaces)

    return InferenceLookupResult(
        matches      = matches,
        interfaces   = interfaces,
        future       = future,
        fullmatch    = current fullmatch,
        unordered    = current ambiguity or future is nonempty,
        valid_worlds = intersection of all contributing queries' validity)
```

The copy passed to ordinary dispatch resolution may be reordered and filtered.
The raw Method list used by `resolve_call_extensibility` must not be filtered;
the separate callee list is the target of future-region filtering.

`resolve_call_extensibility` converts its selected interface regions directly
into positive `AnyFutureMethodMatch` bounds, coalescing equivalent regions where
sound, and removes current callees fully covered by those bounds. Return
contracts remain in the separate `interfaces` list. Inference can therefore
derive a cumulative bound for either a real callee or a future region without
conflating a dispatch-table target with the contracts which constrain it.

The semantic comparisons used by this algorithm are only:

```text
atype ∩ signature
I ≺: M
package-owner portion within current self rights
package-owner factor closed in the realized package graph
productivity of R
intersection of return-contract bounds
```

Cross-table specificity is always tested directly between the interface and
Method. It is not inferred transitively from either table's interference graph.

## Current implementation boundary

The runtime now supplies unfiltered Method and interface intersection queries,
constructs `Core.InterfaceMatch` directly, and records the directional
cross-table interference relation. Compiler implements the positive
`resolve_call_extensibility` fixed point and fixed-callee filtering above.

Raw intersection collection uses its own typemap visitor. It shares world
validation and `MethodMatch` construction with ordinary `ml_matches`, but has
no conditional paths for limits, fully-covering early returns, ambiguity,
dominance, or typemap slurping. This makes completeness a property of the raw
collector rather than an opt-out mode of the dispatch collector.

The equations remain the exact semantic specification. Julia types generally
do not represent `M ∖ Oₘ` directly, and exact partitioning by all intersections
may be exponentially expensive. The current positive algorithm deliberately
returns interface regions as a conservative upper bound.

The Compiler-level semantic representation is:

```text
AnyFutureMethodMatch:
    spec_types       query-local positive upper bound on a future target

InferenceLookupResult:
    matches          real current callees safe to explore as fixed targets
    future           possible future dispatch-table targets
    interfaces       every applicable cumulative interface contract
    valid_worlds     intersection of every contributing lookup
    fullmatch        current Method coverage, before future filtering
    unordered        current ambiguity or any future target
```

`inference_matches` accepts the current incremental output transaction's
ownership-rights formula. It does not enumerate future authorities or invert a
package formula into type regions. During incremental output it applies the
all-or-nothing first-argument gate described above. At ordinary runtime the gate
is bypassed without querying the package graph.

When the gate succeeds, the implementation runs `resolve_call_extensibility`
once over the resolved callees, all raw Methods, and all interfaces. Selected
query-local interface regions become conservative positive future bounds
directly. Regions whose `packagetype` lower bound is bottom are omitted under
the current productivity policy.

A current callee is removed only when its complete query-local `spec_types` is
covered by the union of future regions. `fullmatch` remains the current Method
coverage result before that filtering. Any current ambiguity or nonempty future
list marks the complete call `unordered`; interface contracts by themselves do
not change Method ordering, though optimizer lowering must separately preserve
their runtime assertions.

## First-argument dispatch closure

`arg0_package_owner(T)` computes the positive package formula which closes the
callable first-argument region. For an ordinary DataType it reads the finalized
`TypeName.dispatch_closed_in` root. A TypeName with `dispatch_closed_in ===
nothing` is wide open, `Union{}` has no call region, and unions join the owner
formulas of their arms. Closure inherited from an abstract supertype therefore
continues to close callable subtypes defined by another package.

Constructor-like `Type{T}` regions use a distinct exact operation. Their owner
is the module of the TypeName directly named by `T`; nominal supertypes are not
charged. Thus a subtype created in `Q` remains owned by `Q` for exact
constructor dispatch even when its supertype comes from `P`. A stable exact
`Type{Union{A,B}}` meets the direct owners of its surviving arms. The proof
reuses `packagetype`'s semantic subsumption, arm-bottomability, and independent
orthogonality checks. If representation stability is not proved and all
possible arm formulas are not already equivalent, the constructor region is
conservatively wide open.

Neither operation canonicalizes its package formula using `≤R`.

During incremental output, `_package_owner_is_closed_or_self` checks every DNF
portion independently. A portion is self-owned when it implies an alternative
in the current transaction's ownership rights. Otherwise it is closed only when
it is nonempty and every factor identifies a closed `LoadedPackageNode` in the
realized package graph. This is a direct node-state query; `≤R` reachability is
not consulted.

The graph's ordinary notion of module openness is intentionally not applied at
ordinary runtime. Runtime inference treats the gate as satisfied and relies on
normal method-table invalidation. This avoids interpreting the deliberate
runtime reopening of modules as a reason to discard all fixed callees.

The following work remains outside the semantic query layer:

```text
supplying current transaction ownership rights to inference consumers
sharing one raw Method traversal with ordinary ml_matches resolution
defining global-table semantics for overlay method tables
wiring InferenceLookupResult into inference and optimizer consumers
recording and revalidating the precise Method/interface/ownership edges
```

Any later refinement must preserve two directions:

```text
return a whole-atype AnyFutureMethodMatch whenever an incremental-output
arg0 owner portion is neither closed nor self

emit a conservative AnyFutureMethodMatch whenever an open productive
interface subregion cannot be excluded after the owner gate succeeds
```

The approximation strategy does not alter the pointwise coinductive semantics
recorded here.

## Callee-side contract enforcement

Callee-side interface enforcement is currently an all-or-nothing property of a
CodeInstance. This is required by the existing invalidation scheme: interface
insertion and removal can test whether a CI embeds the complete applicable
interface set, but do not record which individual interfaces or return regions
the CI embeds. A future granular enforcement policy must first introduce
correspondingly granular invalidation facts.

The mode is selected before inference consumes interface contracts. An
unenforced CI therefore contains no interface-derived return, exception,
effect, or IR facts. The positive bit is published only after the optimizer's
inlining stage has materialized the complete selected policy.
