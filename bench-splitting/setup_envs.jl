# Creates the two package environments the sweep uses:
#   envs/fixed — the local ReverseDiff.jl clone (const fields + @noinline ops:
#                the few-giant-blocks IR shape) plus ForwardDiff
#   envs/stock — registry ReverseDiff v1.17.0 (fully-inlined ops: the
#                many-small-blocks IR shape)
using Pkg
Pkg.activate(joinpath(@__DIR__, "envs", "fixed"))
Pkg.develop(path=expanduser("~/repos/ReverseDiff.jl"))
Pkg.add("ForwardDiff")
Pkg.activate(joinpath(@__DIR__, "envs", "stock"))
Pkg.add(name="ReverseDiff", version="1.17.0")
Pkg.status()
