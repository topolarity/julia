# Inference Matches and Interface Openness

This note records the pointwise semantics of interface openness and the
high-level structure of the inference lookup that combines Methods and
interfaces. It also records the conservative positive fixed point used when
Julia cannot represent the required type differences directly.

## Pointwise implementation policy

Fix a concrete call type `ϵ` and an implementation authority `A` (normally a
package root together with its explicitly granted ownership regions). Let:

```text
Pϵ = externally owned Methods applicable at ϵ
Nϵ = interfaces applicable at ϵ and usable by A
```

Same-package-root Methods are omitted from `Pϵ`, since they do not restrict the
package's own implementation rights.

The direct policy relation is:

```text
I ≺: M     ⇒ interface I defeats and opens Method M
I ≺/: M    ⇒ Method M wins and remains closed against I
```

In particular, an equal-signature interface does not open a Method. The
interface must be strictly more specific according to the implementation-policy
specificity relation.

The call type is open precisely when every applicable Method is defeated by at
least one usable interface:

```text
openₐ(ϵ) ⇔ ∀M ∈ Pϵ, ∃I ∈ Nϵ such that I ≺: M
```

Equivalently, it is closed when some Method is undefeated:

```text
closedₐ(ϵ) ⇔ ∃M ∈ Pϵ, ∀I ∈ Nϵ, I ≺/: M
```

Thus the usable interfaces must form a directed dominating set for the
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

Then pointwise openness is the monotone CNF formula:

```text
openₐ(ϵ) = ⋀ₘ ⋁ᵢ rᵢₘ
```

Each Method contributes one clause saying that at least one interface must open
it. Closedness is the De Morgan dual:

```text
closedₐ(ϵ) = ⋁ₘ ⋀ᵢ ¬rᵢₘ
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

To compute `νT`, begin with every usable interface provisionally effective:

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

## Lift from points to type regions

Let `Gₐ` be the region in which authority `A` is otherwise permitted to add an
implementation. For every raw intersecting Method `M`, define its interface-open
region:

```text
Oₘ = ⋃ { I ∩ Gₐ │ I is usable by A and I ≺: M }
```

The portion which remains closed by `M` is:

```text
Cₘ = (M ∩ Gₐ) ∖ Oₘ
```

The complete closed and open regions are:

```text
Closedₐ = ⋃ₘ Cₘ

Openₐ = Gₐ ∖ Closedₐ
       = Gₐ ∩ ⋂ₘ (¬M ∪ Oₘ)
```

A proposed Method signature `R` is admitted exactly when:

```text
R <: Gₐ

∀M:
    R ∩ M <: Oₘ
```

The second form is the complement-free specification of definition-time
admission. Determining whether `Openₐ` has any productive intersection with an
abstract inference query is the dual existence problem. How to approximate that
query with Julia's positive type operations is intentionally deferred.

## Positive `interface_matches` computation

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

For one implementation authority, `interface_matches` receives:

```text
Methods     = every raw applicable Method owned outside the authority
Interfaces  = every raw applicable interface usable by the authority
```

The inputs are query-local matches and must not have been filtered by ordinary
dispatch. An interface is represented as:

```text
InterfaceMatch(
    match    = its query-local MethodMatch,
    rettype  = its return contract instantiated in match.sparams)
```

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
`InterfaceMatch` result, so contract processing and every authority-specific
fixed point can share the same ordered matches.

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
the computation immediately. No expensive cleanup pass is performed: merely
shrinking the returned list would not shrink its represented open region.

The result guarantees:

```text
the actual open dispatch region ⊆ R(OpenInterfaces)
```

where `R` is the union of the returned query-local interface regions. A callee
whose whole `spec_types` is covered by this union must be removed from the
fixed-callee list. Synthesis of `AnyFutureMethodMatch` values from the selected
interfaces remains a separate step.

## High-level inference lookup

The lookup keeps current dispatch resolution separate from future
implementation policy:

```text
inference_matches(atype, world, limit):
    raw_methods    := intersect every live Method with atype at world
    raw_interfaces := intersect every live interface with atype at world

    current := resolve ordinary dispatch on a copy of raw_methods
               using the existing Method-only sorting, ambiguity, coverage,
               SCC, and limit rules

    matches := current.matches

    interfaces := form InterfaceMatch values from raw_interfaces,
                  including their effective narrowed return contracts

    open_interfaces := for each implementation authority A:
                           interface_matches(
                               externally owned raw_methods,
                               interfaces usable by A)

    matches := remove matches covered by open_interfaces

    open := synthesize AnyFutureMethodMatch values from open_interfaces,
            ownership regions, and applicable interface contracts

    return InferenceLookupResult(
        matches      = matches,
        interfaces   = interfaces,
        open         = open,
        fullmatch    = current fullmatch,
        unordered    = current ambiguity or open is nonempty,
        valid_worlds = intersection of both table queries' validity)
```

The copy passed to ordinary dispatch resolution may be reordered and filtered.
The raw Method list used by `interface_matches` must not be filtered.

For each implementation authority `A`, exact future synthesis is specified by:

```text
future_matches(atype, raw_methods, interfaces, A):
    Gₐ := the portion of atype granted to A

    for every raw Method M:
        Oₘ := ⋃ { I ∩ Gₐ │
                  I is a raw applicable interface,
                  I is usable by A,
                  I ≺: M }

        Cₘ := (M ∩ Gₐ) ∖ Oₘ

    Openₐ := Gₐ ∖ ⋃ₘ Cₘ

    partition Openₐ by its applicable interface-contract bounds

    for every productive nonempty partition R:
        emit AnyFutureMethodMatch(R, contract_bound(R))
```

Future matches for all possible authorities are unioned, with equivalent regions
and contract bounds coalesced where sound.

The semantic comparisons used by this algorithm are only:

```text
atype ∩ signature
I ≺: M
same-PackageRoot / implementation-authority admission
R <: Gₐ
R ∩ M <: Oₘ
productivity of R
intersection of return-contract bounds
```

Cross-table specificity is always tested directly between the interface and
Method. It is not inferred transitively from either table's interference graph.

## Current implementation boundary

The runtime now supplies unfiltered Method and interface intersection queries,
constructs `Core.InterfaceMatch` directly, and records the directional
cross-table interference relation. Compiler implements the positive
`interface_matches` fixed point above, plus fixed-callee filtering.

Raw intersection collection uses its own typemap visitor. It shares world
validation and `MethodMatch` construction with ordinary `ml_matches`, but has
no conditional paths for limits, fully-covering early returns, ambiguity,
dominance, or typemap slurping. This makes completeness a property of the raw
collector rather than an opt-out mode of the dispatch collector.

The equations remain the exact semantic specification. Julia types generally
do not represent `M ∖ Oₘ` or `Gₐ ∖ Closedₐ` directly, and exact partitioning by
all intersections may be exponentially expensive. The current positive
algorithm deliberately returns interface regions as a conservative upper bound.

The following work is deferred to inference integration:

```text
enumerating implementation authorities and applying ownership filters
synthesizing AnyFutureMethodMatch values and their contract bounds
combining validity, fullmatch, and unordered state
wiring the result into inference and optimizer consumers
```

Any later refinement must preserve two directions:

```text
omit AnyFutureMethodMatch only after proving the region fully covered

emit a conservative AnyFutureMethodMatch whenever an open productive
subregion cannot be excluded
```

The approximation strategy does not alter the pointwise coinductive semantics
recorded here.
