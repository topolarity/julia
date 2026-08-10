# Requires graph, ownership, and image regions

**Status:** design for the initial package-graph implementation and its planned
loading/pkgimage follow-ups.

This note separates three concepts which are related operationally but have
different identities and ordering rules:

1. declared and realized package dependencies;
2. the ownership authority used to classify and admit declarations;
3. the image regions needed to precompile degenerate extension configurations
   without avoidable runtime invalidation.

The initial implementation constructs the package-graph substrate needed by the
ownership policy. It must remain compatible with region-based images, but
ownership grants, region-based loading, and region-based precompilation are
follow-up work.

## Semantic layers

| Layer | Nodes or data | Meaning |
| --- | --- | --- |
| Declared graph, `≤D` | `Base.PkgId` | Ordinary dependency edges permitted by Project/Manifest resolution |
| Requires graph, `≤R` | `LoadedPackageNode` | Actual attributed `require`, `using`, and `import` edges |
| Extension metadata | `ExtensionSpec` | Parent, triggers, and dependency-resolution context |
| Ownership policy | Unions of formal intersections | Authority used to classify and admit methods and interfaces |
| Image graph | Future region/image nodes | Operational grouping required to internalize degeneracy invalidations |

The precompilation scheduler's `direct_deps` is not one of these semantic
graphs. It is always a scheduling approximation. For ordinary packages it
starts from declared dependencies that may never be loaded, and it is further
augmented with derived extension and scheduling edges. The same restriction
applies to its extension entries.

## Package identities and loaded instances

The identity-level key is the existing `Base.PkgId`. A separate `PackageKey`
type is unnecessary and would duplicate the identity already used by package
resolution, cache headers, extension metadata, and `Base.require`.

A `LoadedPackageNode` represents one loaded root-module instance. This
distinction is necessary even though ordinary `require` exposes one canonical
module per `PkgId`: replaced modules and multiple restored precompile instances
can coexist in one process.

Conceptually:

```julia
pkgid(node::LoadedPackageNode) = PkgId(node.root_module)
```

Node equality is instance identity, not `PkgId` equality. The future scheduler
design will require the projection from loaded instances to declared identities
to satisfy the direct-edge refinement invariant:

```text
X →R Y  implies  pkgid(X) →D pkgid(Y)
```

The first pass does not enforce this invariant because no current policy or
scheduling consumer relies on it. When it becomes meaningful, it must be part
of cache/scheduler validation rather than an incidental post-restoration check.

Reachability in both graphs is treated as a preorder unless acyclicity is
independently established. Core, Base, and Main may require explicit axiomatic
or unmanaged treatment rather than fabricated Manifest edges.

## The declared graph

The declared graph records permission to create ordinary dependency edges. It
is derived independently from the environment's Project and Manifest data and
retains direct adjacency as well as transitive reachability queries.

This graph is a may-require bound. A declared edge does not imply that its
target is loaded, imported, initialized, required, or present in a package
image.

The declared dependency graph and the requires graph are distinct values. They
are not substituted for one another, and `Precompilation.direct_deps` is not
used as the source of either graph.

## The requires graph

The requires graph contains simple `LoadedPackageNode`s and direct requirement
edges. Its transitive closure defines `≤R`.

Edges arise from:

- `using` and `import` evaluated through the ordinary lowering/loading path;
- direct `Core._using` or `Core._import` calls, which must not bypass recording;
- attributed `Base.require`-like operations that return an accessible package
  module and establish a package requirement.

Package loading and namespace binding are currently split between
`Base.require` and Core's import builtins. Instrumentation must give these paths
a unified, idempotent graph view. Merely observing that two packages or images
are loaded does not create a requires edge between them.

The first implementation admits a novel outgoing requirement exactly when the
source package's module is open. When it is closed, only idempotent
repetitions of an existing edge remain valid. This deliberately follows Julia's
existing context-sensitive module policy rather than imposing a stronger
static-runtime restriction in the first pass.

### First-pass representation and openness

The realized direct adjacency is stored in a `package_requires` field on each
root `jl_module_t`. The field is a serialized vector of target root-module
references, rather than a hidden Julia binding. This both preserves exact
loaded-instance identity across external module relocations and avoids exposing
policy state through a forgeable module binding. The runtime GC implementations
scan the field, and the image serializer restores it as ordinary module state.

`LoadedPackageNode` equality is exact root-module identity. The compiler's
requires-graph traversal consequently uses `IdSet`. The declared graph uses
`IdDict{PkgId,...}`: `PkgId` is immutable and its current `UUID`/`Nothing` and
`String` fields give it value `===` semantics, so independently reconstructed
equal keys coalesce without requiring `Base.Dict` during compiler bootstrap.

A managed package instance may add novel outgoing edges exactly while its
module is open according to the runtime. All of its submodules share the same
`LoadedPackageNode` and coincident openness. The runtime openness query first
canonicalizes any module argument to its registered root module, using the same
root boundary as `Base.moduleroot` (including roots such as `Base.Compiler`
whose parent pointer alone is insufficient). Openness therefore cannot diverge
between a package and one of its submodules.

Root modules record a distinct monotonic `finalized` fact when their source
construction transaction is complete. Finalization is not itself openness:
openness is derived from finalization and the current execution context. This
is deliberately instance-relative and context-sensitive:

- outside incremental output generation, all modules are open, including while
  final-application initializers and later runtime code execute;
- during incremental output generation, an unfinalized root belonging to the
  current output transaction is open;
- during incremental output generation, a finalized root is closed even when
  its modules remain in an initializer worklist; and
- restored dependency modules do not belong to that transaction and are closed
  while their initializers run during downstream precompilation, where their
  heap side effects are largely discarded.

The requires graph is not independently reopened for every call to `__init__`.
At final runtime, it is the ordinary policy that reopens every module. A
restored instance starts with the requirements serialized from the precompile
instance and may then acquire more requirements under that runtime policy.

### Relationship to module initialization order

The runtime notion of module openness is the union of two cases:

1. Julia is not generating incremental output, in which case every module is
   open; or
2. Julia is generating incremental output, the root is not finalized, and it
   belongs to the current output transaction.

During incremental output generation, `jl_current_modules` contains modules
whose top-level evaluation is active. `jl_module_init_order` retains newly
completed modules in definition-finished order so they can later be serialized
as the current image's module worklist. A root can be finalized while its
modules remain in this list, which is necessary when one output transaction
builds more than one package. For a managed root, being unfinalized implies
membership in the current output transaction; the runtime treats violation of
that implication as an internal invariant failure rather than another semantic
openness state. At compiler-output finalization, the list is filtered to
modules which actually define `__init__` and serialized as the initializer
order.

Restoring an incremental image yields a separate image-local initializer vector
which `Base.register_restored_modules` executes directly. It is not merged into
the current output transaction. Consequently, dependency initializers executed
during downstream precompilation see closed dependency modules, whereas the
same initializers at final runtime see every module open.

This tracking is useful for defining the shared openness predicate, but it is
not itself the requires graph: it is module-granular, includes submodules, is an
ordered worklist rather than an edge relation, and changes roles during output
finalization. The requires graph therefore remains root-package-granular and
stores its own adjacency while reusing the runtime's openness decision.

Ordinary `Base.require(into, name)`, `Core._using`, and `Core._import` share the
same Julia policy hooks. Core and Base are axiomatic targets, as is the exact
sysimage `Base.Compiler` module when accessed through Base; this last exception
preserves the supported `using Base.Compiler` path without granting the same
status to a separately loaded Compiler instance. Unmanaged roots such as Main
do not publish graph edges.

The first pass treats the unattributed internal `Base.require(PkgId)` API and
other reflective access to loader internals as privileged implementation
mechanisms, not ordinary package visibility operations. Code which creates a
semantic requirement must use an attributed require/import operation. A future
loader API cleanup can make this distinction structural rather than
conventional.

## Extensions remain simple package nodes

An extension `E` has an ordinary `PkgId`, an ordinary `LoadedPackageNode`, and
ordinary explicit requirement edges. Its parent and triggers do not create
`≤R` edges. In particular, two extensions activated by the same trigger set
receive no mutual visibility or ordering:

```text
E1 !≤R E2
E2 !≤R E1
```

unless an explicit ordinary edge establishes one of those relations.

Extension activation metadata is retained separately:

```julia
struct ExtensionSpec
    extension::PkgId
    parent::PkgId
    triggers::Vector{PkgId}
end
```

This metadata is needed to:

- activate the extension;
- derive which ordinary dependencies the extension is permitted to load;
- construct its ownership rights;
- detect image degeneracy;
- construct future region images;
- validate cached policy inputs.

Under the current resolver, an extension's dependency permissions are derived
from its parent's ordinary dependencies together with the weak dependencies
that trigger that extension. This bounds possible ordinary edges but does not
synthesize realized edges. Future extension-owned dependencies can extend the
permission model without changing the simple-node representation.

An extension's `PkgId` is derived from its parent identity and extension name;
it does not encode its trigger set. Activation metadata therefore cannot be
recovered from extension identity alone.

## Ownership is distinct from the requires graph

Ownership authority is represented as a union of formal intersection portions.
The intended data model is equivalent to:

```julia
struct OwnershipPortion{N}
    factors::Vector{N}
end

struct OwnershipRights{N}
    alternatives::Vector{OwnershipPortion{N}}
end
```

An ordinary package `P` has its intrinsic singleton right:

```text
ownership(P) = P
```

An extension `E` of `P` triggered by `A` and `B` has:

```text
ownership(E) = E union (P & A & B)
```

The singleton `E` right gives the extension ordinary ownership of declarations
involving types it introduces. The additional intersection portion gives it the
intended extension/type-piracy authority without inventing requires edges.

Ownership portions have intensional, provenance-preserving identity. Their
factors may be sorted and deduplicated, but they must not be simplified using
`≤R`:

```text
P & A & B != P
```

even when `P ≤R A` and `P ≤R B`. Such portions may have the same operational
load footprint while remaining distinct policy portions.

Available ownership rights may be supplied symbolically to a precompile or
source-definition transaction before all factors have been loaded. A dormant
right cannot justify a declaration unless the declaration actually exercises
the corresponding ownership portion. In particular, an unused trigger must not
act as a generic license for a declaration whose ownership support omits that
factor.

The ownership grant belongs to the definition transaction:

- a precompile worker receives it before evaluating the package or extension;
- a direct source load receives it before source definitions are evaluated;
- pkgimage loading validates the policy context under which cached
  declarations and inference were produced rather than granting authority for
  the first time.

The defining `LoadedPackageNode` and the ownership portion are separate facts.
This preserves package-locality and diagnostics when multiple independently
authored packages receive the same intersection authority.

## First-pass definition enforcement

Each root `Module` stores its normalized implementation-rights formula. Root
registration initializes the field before package source evaluation: an
ordinary package receives `P`, while an extension receives its singleton `E`
right plus any trigger intersection whose factors identify loaded package
instances. Submodules query the same root field. Unmanaged roots such as an
interactive application are unrestricted. If an intersection is initially
dormant, successful requires-edge publication refreshes the stored grant before
package evaluation continues. Rights updates acquire `jl_method_def_lock` while
already holding `require_lock`; definition classification never takes the
loading lock, preserving this lock order.

Parallel precompilation passes an extension's declared parent/trigger set
explicitly into its compile worker. This set is stored separately from the
precompilation scheduler's trigger/dependency graph: scheduling may add other
extensions to that graph, but those derived edges are not ownership inputs.
Conflating them would grant authority based on a scheduling approximation.

Before publishing a global Method or interface Method, definition policy checks:

1. the upper bound of `packagetype(signature)` implies one of the defining
   root's implementation rights;
2. a definition over any externally closed first-argument portion is a subtype
   of an interface (a candidate interface is its own witness); and
3. whenever the candidate is more specific than an existing Method from a
   different package root, one of those covering interfaces is also more
   specific than that Method.

Existing Methods from the defining package root do not consume its interface
permission. This permits a package to add both a broad and a narrow local
implementation under one upstream interface. Independently loaded sibling
implementations may still introduce ambiguity in their downstream
intersection; definition admission does not attempt to predict or forbid that
intersection.

`jl_method_def_lock` serializes the complete policy snapshot with publication
to the ordinary and interface tables. Classification reads the already stored
root rights and therefore does not acquire the loading lock while holding the
definition lock. Diagnostics are emitted after releasing the lock. The command
line policy is `--piracy={strict|warn|off}`, defaulting to `warn`; warning and
off modes preserve normal dispatch, while strict mode rejects the definition
before publication.

The first implementation intentionally uses the current unrestricted `≺:`
relation. Restricting cross-package specificity with the requires graph is
deferred until the inference/edge work; until then, admission alone cannot
provide the intended no-invalidation guarantee.

## Ownership rights are cache inputs

The complete normalized ownership context used to classify declarations is a
pkgimage input. It is not sufficient to key only on the loaded package
identities or build IDs.

For example, the same method can change classification without changing its
signature or referenced modules:

```text
rights = E
    => method is impl piracy

rights = E union (P & A & B)
    => method is owned/non-piratical
```

That classification can affect:

- whether a later specialization is permitted;
- whether a call region is closed;
- whether an `AnyFutureMethodMatch` is required;
- which policy dependencies inference records;
- which subsequent changes invalidate compiled code.

The initial cache-policy implementation should conservatively key on the full
normalized ownership-rights expression. Query-sensitive dependency tracking may
later reduce this input, but it is an optimization rather than a semantic
change.

Current cache checks often detect a changed extension environment indirectly
when trigger packages are explicitly imported and therefore appear in recorded
`require` mappings. That is not complete: an ownership factor can affect policy
without producing such an import. General graph/policy staleness checking must
therefore include the ownership context explicitly.

This cache integration is follow-up loading/pkgimage work. Until it is present,
the graph implementation must not claim that existing package-oriented cache
keys validate rights-dependent policy facts across environments.

## Precise inference during the interim

The absence of another known member of a future image region is construction
incompleteness, not semantic openness.

`AnyFutureMethodMatch` represents an inherently legal unknown future selected
callee under the final ownership/interface policy. It must not be synthesized
merely because a separately precompiled member of the same degenerate region
has not loaded yet.

Instead, each current package image receives ordinary precise current-world
inference. Later packages and extensions publish their methods and interfaces
and invalidate exactly the affected compiled code:

```text
compile E1 precisely
load E2 later
invalidate affected E1 inference
reinfer on demand with the final visible declarations
```

This applies equally to an extension calling its own concrete methods and to a
package in a self-degenerate package/extension configuration. The interim cost
is additional runtime invalidation, not approximate inference quality.

Required dependency channels include ordinary positive and negative method
facts, interface-table facts, and any package-graph/policy fact consulted by
inference. Region-based images will move degeneracy-related invalidations into
the shared image build rather than unlock inference capabilities withheld from
separate images.

## Degeneracy and future image regions

Image degeneracy is an operational relation and does not canonicalize package
nodes or ownership portions.

Two extensions with the same complete activation-factor set--for example, the
same parent and triggers `{P, A, B}`--have distinct package nodes and the same
formal `P & A & B` ownership portion. They must eventually be compiled in one
`P & A & B` region image so that their method definitions share an evolving
method-table world before the image is serialized. They do not thereby acquire
import rights to one another.

A self-degenerate extension illustrates why operational degeneracy and ownership
identity differ. If `P` already loads every trigger of extension `E`, then `E`
always activates when `P` loads. Operationally, `P` and `E` must eventually be
members of the same image. Nevertheless, the intersection ownership portion
remains distinct from `P` and is not simplified away.

Future image construction cannot derive all operational regions before a build
starts. The declared graph only bounds the requires graph, and two packages
with the same declared dependencies can establish different requirements while
their source is evaluated. Region membership must therefore be discovered as
part of image construction rather than predicted from `≤D`.

### Advancing construction frontier

The precompilation scheduler should maintain an advancing construction
frontier. Behind the frontier, every package has complete and frozen outgoing
`≤R` edges and every target of such an edge is either also behind the frontier
or belongs to the same open region transaction. Only the roots in the current
round have unknown outgoing requirements. Subject to the later extension
stratification work, rounds are downward-closed in `≤D`, so a root cannot
discover an unprepared dependency while it is being evaluated.

A build proceeds as follows:

1. prepare every declared dependency which may be needed by the next roots or
   by an extension that those roots may activate;
2. enqueue a root with an open, uncommitted image transaction;
3. evaluate it while recording its actual `require`, `using`, and `import`
   edges and running extension activation to a fixed point;
4. dynamically grow the open transaction to include extensions which become
   degenerate with it;
5. freeze its realized requirements and atomically advance the construction
   frontier when the transaction is serialized;
6. enqueue any extension activation context not already covered by a grown
   transaction, again using an open transaction which may grow to include
   degenerate peer extensions.

The scheduler must coordinate extension claims so that an extension absorbed
by a growing package transaction is not also finalized by an independently
scheduled extension job. It may conservatively delay such jobs until the
relevant package round reports its realized activation closure. False-positive
`≤D` relations can consequently reduce parallelism or schedule unnecessary
work, but cannot combine images.

Preparing or loading a dependency is not the same operation as requiring it
from a particular root. Only an attributed `require`, `using`, or `import`
operation adds a `≤R` edge. This distinction allows `≤D` to serve as the
scheduling bound without making its false-positive edges semantically visible.

An image transaction is combined from the beginning even when its complete
membership is not known before its first statement executes: all dynamically
added members are evaluated in the same evolving method-table world before any
member is finalized. Ordinary invalidation during the transaction repairs
inference performed before a later member was activated. No assembly of
separately finalized package images or separate final inference pass is
required.

Once a transaction is sealed, later co-loading of independent images creates a
new intersection region above those images; it does not retroactively change
their outgoing edges or merge them. Conversely, if a root's own requirements
make an extension degenerate with that root, the relevant edges and activation are
observed while the root transaction is still open. This causal property is what
makes the advancing frontier possible.

Treating every declared dependency as loaded would make the regions knowable
in advance, but is not an acceptable alternative. It would force packages to
load dependencies which they intentionally leave unloaded for latency,
extension activation, legacy type-piracy, or side-effect reasons. The desired
compositionality of package method definitions does not make those loading and
initialization effects unobservable.

Region images are not assembled from independently finalized package images.
All members are evaluated in one image-building process with shared world-age
and invalidation bookkeeping. A separate final inference phase is not required:
ordinary invalidation during image construction is sufficient to ensure that
serialized inference is valid for the final build world.

The implementation may choose a deterministic source/build order for
reproducibility. Such an order is not a semantic `≤R` edge and does not confer
namespace visibility.

The semantic image/region node should remain distinct from both a
`LoadedPackageNode` and the physical `.ji`/native artifact which materializes
it. A package's image membership is environment-relative and must not be an
intrinsic permanent field of the package node.

## Initial implementation scope

The first `ct/package-graph` implementation provides:

1. a bootstrap-safe `Base.PkgId`-keyed declared-graph value type;
2. instance-based `LoadedPackageNode`s and a process-wide requires-graph view;
3. direct and transitive `≤D` and `≤R` queries;
4. unified, idempotent recording of attributed `require`, `using`, and `import`
   edges;
5. serialized requires adjacency on each root module;
6. outgoing-edge admission tied directly to the module's existing
   context-sensitive openness; and
7. tests covering declared-key identity, source loading, final-application
   initialization, downstream-precompile closure, pkgimage restoration,
   reachability, and final-runtime reopening.

This pass does not yet materialize a complete declared-graph snapshot from a
Manifest, enforce `→R` refinement of `→D`, construct extension metadata or
formal ownership grants, key images on those policy inputs, or implement
region-based precompilation. Those remain separate layers described above.

## Explicit loading and pkgimage follow-ups

The following work is required to realize all intended guarantees:

- key pkgimages on normalized ownership rights and all graph-policy assumptions
  that affect serialized declarations or inference;
- materialize the applicable declared graph and validate `→R` refinement of
  `→D` once scheduling or policy begins to rely on that relation;
- record and validate extension activation provenance where it affects policy;
- key region images on their complete activation specification, membership,
  lower-region build identities, and ordinary cache inputs;
- replace package-oriented precompile jobs with canonical region-oriented jobs;
- compile each region as one genuinely combined multi-module image;
- tighten extension activation failure and atomic-publication behavior;
- reconcile source-loading, restored-image, and initializer phase behavior;
- support extension-owned dependencies and stratify extension/image activation
  to control operational cycles;
- add precise invalidation for interface and graph-policy dependencies;
- preserve normal current-world inference while separate images remain the
  implementation.

These limitations are performance and activation-atomicity compromises. They
must not be converted into defensive `AnyFutureMethodMatch` results or other
inference-quality regressions.
