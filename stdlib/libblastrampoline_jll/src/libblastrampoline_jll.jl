# This file is a part of Julia. License is MIT: https://julialang.org/license

## dummy stub for https://github.com/JuliaBinaryWrappers/libblastrampoline_jll.jl

baremodule libblastrampoline_jll
using Base, Libdl

export libblastrampoline

# These get calculated in __init__()
const PATH = Ref("")
const PATH_list = String[]
const LIBPATH = Ref("")
const LIBPATH_list = String[]
artifact_dir::String = ""

# Because LBT needs to have a weak-dependence on OpenBLAS (or any other BLAS)
# we must manually construct a list of which modules and libraries we're going
# to be using with it, as well as the on load callbacks they may or may not need.
#
# The registered callbacks are stored type-erased (see `Libdl.ErasedCallable`)
# so that dispatching them involves no dynamic call and this chain stays
# statically compileable (e.g. under `--trim`).
const on_load_callbacks::Vector{Libdl.ErasedCallable} = Libdl.ErasedCallable[]
const eager_mode_modules::Vector{Module} = Module[]
function libblastrampoline_on_load_callback()
    for callback = on_load_callbacks
        callback()
    end
end

function add_dependency!(mod::Module, lib::LazyLibrary,
                         on_load_callback::Union{Function, Libdl.ErasedCallable, Nothing} = nothing)
    Libdl.add_dependency!(libblastrampoline, lib)
    push!(eager_mode_modules, mod)
    if on_load_callback !== nothing
        push!(on_load_callbacks, on_load_callback isa Libdl.ErasedCallable ?
            on_load_callback : Libdl.ErasedCallable(on_load_callback))
    end
    return nothing
end

libblastrampoline_path::String = ""
# NOTE: keep in sync with `Base.libblas_name` and `Base.liblapack_name`.
const libblastrampoline_soname = if Sys.iswindows()
        "libblastrampoline-5.dll"
    elseif Sys.isapple()
        "libblastrampoline.5.dylib"
    else
        "libblastrampoline.so.5"
    end
const libblastrampoline = LazyLibrary(
    BundledLazyLibraryPath(libblastrampoline_soname);
    # uuid5(<package uuid>, "libblastrampoline")
    id = Base.UUID("4114344b-adca-5d9d-b4ae-fbb7c6187582"),
    dependencies = LazyLibrary[],
    on_load_callback = libblastrampoline_on_load_callback
)

function eager_mode()
    for mod in eager_mode_modules
        mod.eager_mode()
    end
    dlopen(libblastrampoline)
end
is_available() = true

function __init__()
    # The type-erased callback pointer is process-local and does not survive
    # precompile serialization; re-arm it before any dlopen can occur.
    Libdl.init_callable!(libblastrampoline.on_load_callback::Libdl.ErasedCallable,
                         @cfunction(libblastrampoline_on_load_callback, Any, ()))
    global libblastrampoline_path = string(libblastrampoline.path)
    global artifact_dir = dirname(Sys.BINDIR)
    LIBPATH[] = dirname(libblastrampoline_path)
    push!(LIBPATH_list, LIBPATH[])
end

if Base.generating_output()
    precompile(eager_mode, ())
    precompile(is_available, ())
end

end  # module libblastrampoline_jll
