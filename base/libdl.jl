# This file is a part of Julia. License is MIT: https://julialang.org/license

module Libdl
@doc """
Interface to libdl. Provides dynamic linking support.
""" Libdl

import Base: DL_LOAD_PATH, isdebugbuild

export DL_LOAD_PATH, RTLD_DEEPBIND, RTLD_FIRST, RTLD_GLOBAL, RTLD_LAZY, RTLD_LOCAL,
    RTLD_NODELETE, RTLD_NOLOAD, RTLD_NOW, dlclose, dlopen, dlopen_e, dlsym, dlsym_e,
    dlpath, find_library, dlext, dllist, LazyLibrary, LazyLibraryPath, BundledLazyLibraryPath

"""
    DL_LOAD_PATH

When calling [`dlopen`](@ref), the paths in this list will be searched first, in
order, before searching the system locations for a valid library handle.
"""
DL_LOAD_PATH

# note: constants to match JL_RTLD_* in src/julia.h, translated
#       to system-specific values by JL_RTLD macro in src/dlload.c
const RTLD_LOCAL     = 0x00000001
const RTLD_GLOBAL    = 0x00000002
const RTLD_LAZY      = 0x00000004
const RTLD_NOW       = 0x00000008
const RTLD_NODELETE  = 0x00000010
const RTLD_NOLOAD    = 0x00000020
const RTLD_DEEPBIND  = 0x00000040
const RTLD_FIRST     = 0x00000080

"""
    RTLD_DEEPBIND
    RTLD_FIRST
    RTLD_GLOBAL
    RTLD_LAZY
    RTLD_LOCAL
    RTLD_NODELETE
    RTLD_NOLOAD
    RTLD_NOW

Enum constant for [`dlopen`](@ref). See your platform man page for details, if
applicable.
"""
(RTLD_DEEPBIND, RTLD_FIRST, RTLD_GLOBAL, RTLD_LAZY, RTLD_LOCAL, RTLD_NODELETE, RTLD_NOLOAD, RTLD_NOW)

# The default flags for `dlopen()`
const default_rtld_flags = RTLD_LAZY | RTLD_DEEPBIND

"""
    dlsym(handle, sym; throw_error::Bool = true)

Look up a symbol from a shared library handle, return callable function pointer on success.

If the symbol cannot be found, this method throws an error, unless the keyword argument
`throw_error` is set to `false`, in which case this method returns `nothing`.
"""
function dlsym(hnd::Ptr, s::Union{Symbol,AbstractString}; throw_error::Bool = true)
    hnd == C_NULL && throw(ArgumentError("NULL library handle"))
    val = Ref(Ptr{Cvoid}(0))
    symbol_found = ccall(:jl_dlsym, Cint,
        (Ptr{Cvoid}, Cstring, Ref{Ptr{Cvoid}}, Cint, Cint),
        hnd, s, val, Int64(throw_error), Int64(1)
    )
    if symbol_found == 0
        return nothing
    end
    return val[]
end

"""
    dlsym_e(handle, sym)

Look up a symbol from a shared library handle, silently return `C_NULL` on lookup failure.
This method is now deprecated in favor of `dlsym(handle, sym; throw_error=false)`.
"""
function dlsym_e(args...)
    return something(dlsym(args...; throw_error=false), C_NULL)
end

"""
    dlopen(libfile::AbstractString [, flags::Integer]; throw_error:Bool = true)

Load a shared library, returning an opaque handle.

The extension given by the constant `dlext` (`.so`, `.dll`, or `.dylib`)
can be omitted from the `libfile` string, as it is automatically appended
if needed.   If `libfile` is not an absolute path name, then the paths
in the array `DL_LOAD_PATH` are searched for `libfile`, followed by the
system load path.

The optional flags argument is a bitwise-or of zero or more of `RTLD_LOCAL`, `RTLD_GLOBAL`,
`RTLD_LAZY`, `RTLD_NOW`, `RTLD_NODELETE`, `RTLD_NOLOAD`, `RTLD_DEEPBIND`, and `RTLD_FIRST`.
These are converted to the corresponding flags of the POSIX (and/or GNU libc and/or MacOS)
dlopen command, if possible, or are ignored if the specified functionality is not available
on the current platform. The default flags are platform specific. On MacOS the default
`dlopen` flags are `RTLD_LAZY|RTLD_DEEPBIND|RTLD_GLOBAL` while on other platforms the
defaults are `RTLD_LAZY|RTLD_DEEPBIND|RTLD_LOCAL`. An important usage of these flags is to
specify non default behavior for when the dynamic library loader binds library references to
exported symbols and if the bound references are put into process local or global scope. For
instance `RTLD_LAZY|RTLD_DEEPBIND|RTLD_GLOBAL` allows the library's symbols to be available
for usage in other shared libraries, addressing situations where there are dependencies
between shared libraries.

If the library cannot be found, this method throws an error, unless the keyword argument
`throw_error` is set to `false`, in which case this method returns `nothing`.

!!! note
     From Julia 1.6 on, this method replaces paths starting with `@executable_path/` with
     the path to the Julia executable, allowing for relocatable relative-path loads. In
     Julia 1.5 and earlier, this only worked on macOS.
"""
function dlopen end

dlopen(s::Symbol, flags::Integer = default_rtld_flags; kwargs...) =
    dlopen(string(s), flags; kwargs...)

function dlopen(s::AbstractString, flags::Integer = default_rtld_flags; throw_error::Bool = true)
    ret = ccall(:jl_load_dynamic_library, Ptr{Cvoid}, (Cstring,UInt32,Cint), s, flags, Cint(throw_error))
    if !throw_error && ret == C_NULL
        return nothing
    end
    return ret
end

"""
    dlopen(f::Function, args...; kwargs...)

Wrapper for usage with `do` blocks to automatically close the dynamic library once
control flow leaves the `do` block scope.

# Examples
```julia
vendor = dlopen("libblas") do lib
    if Libdl.dlsym(lib, :openblas_set_num_threads; throw_error=false) !== nothing
        return :openblas
    else
        return :other
    end
end
```
"""
function dlopen(f::Function, name, args...; kwargs...)
    hdl = nothing
    try
        hdl = dlopen(name, args...; kwargs...)
        f(hdl)
    finally
        dlclose(hdl)
    end
end

"""
    dlopen_e(libfile::AbstractString [, flags::Integer])

Similar to [`dlopen`](@ref), except returns `C_NULL` instead of raising errors.
This method is now deprecated in favor of `dlopen(libfile::AbstractString [, flags::Integer]; throw_error=false)`.
"""
dlopen_e(args...) = something(dlopen(args...; throw_error=false), C_NULL)

"""
    dlclose(handle)

Close shared library referenced by handle.
"""
function dlclose(p::Ptr)
    0 == ccall(:jl_dlclose, Cint, (Ptr{Cvoid},), p)
end

"""
    dlclose(::Nothing)

For the very common usage pattern of

    try
        hdl = dlopen(library_name)
        ... do something
    finally
        dlclose(hdl)
    end

We define a `dlclose()` method that accepts a parameter of type `Nothing`, so
that user code does not have to change its behavior for the case that `library_name`
was not found.
"""
function dlclose(p::Nothing)
end

"""
    find_library(names [, locations])

Searches for the first library in `names` in the paths in the `locations` list,
`DL_LOAD_PATH`, or system library paths (in that order) which can successfully be dlopen'd.
On success, the return value will be one of the names (potentially prefixed by one of the
paths in locations). This string can be assigned to a `global const` and used as the library
name in future `ccall`'s. On failure, it returns the empty string.
"""
function find_library(libnames, extrapaths=String[])
    for lib in libnames
        for path in extrapaths
            l = joinpath(path, lib)
            p = dlopen(l, RTLD_LAZY; throw_error=false)
            if p !== nothing
                dlclose(p)
                return l
            end
        end
        p = dlopen(lib, RTLD_LAZY; throw_error=false)
        if p !== nothing
            dlclose(p)
            return lib
        end
    end
    return ""
end
find_library(libname::Union{Symbol,AbstractString}, extrapaths=String[]) =
    find_library([string(libname)], extrapaths)

"""
    dlpath(handle::Ptr{Cvoid})

Given a library `handle` from `dlopen`, return the full path.
"""
function dlpath(handle::Ptr{Cvoid})
    handle == C_NULL && throw(ArgumentError("NULL library handle"))
    p = ccall(:jl_pathname_for_handle, Cstring, (Ptr{Cvoid},), handle)
    s = unsafe_string(p)
    Sys.iswindows() && Libc.free(p)
    return s
end

"""
    dlpath(libname::Union{AbstractString, Symbol})

Get the full path of the library `libname`.

# Examples
```julia-repl
julia> dlpath("libjulia")
```
"""
function dlpath(libname::Union{AbstractString, Symbol})
    handle = dlopen(libname)
    path = dlpath(handle)
    dlclose(handle)
    return path
end

if Sys.isapple()
    const dlext = "dylib"
elseif Sys.iswindows()
    const dlext = "dll"
else
    #assume Sys.islinux, or similar
    const dlext = "so"
end

"""
    dlext

File extension for dynamic libraries (e.g. dll, dylib, so) on the current platform.
"""
dlext

"""
    dllist()

Return the paths of dynamic libraries currently loaded in a `Vector{String}`.
"""
function dllist()
    dynamic_libraries = Vector{String}()

    @static if Sys.isapple()
        numImages = ccall(:_dyld_image_count, Cint, ())

        # start at 1 instead of 0 to skip self
        for i in 1:numImages-1
            name = unsafe_string(ccall(:_dyld_get_image_name, Cstring, (UInt32,), i))
            push!(dynamic_libraries, name)
        end
    elseif Sys.iswindows() || Sys.islinux() || Sys.isbsd()
        # `dl_iterate_phdr` must be handled by C, since otherwise arbitrary Julia
        # code (in finalizers / ccall symbol resolution) may compete for the dynamic
        # linker lock held during its callback
        ccall(:jl_dllist, Cint, (Any,), dynamic_libraries)
    else
        # unimplemented
    end

    return dynamic_libraries
end


"""
    ErasedCallable(callable)

A nullary callable that is invoked through a type-erased C function pointer,
so that calling it involves no dynamic dispatch. This keeps its callers
statically compileable (e.g. under `--trim`) even when `callable` itself has
an arbitrary type.

The pointer is process-local state: it is created ("armed") from `callable`
when the `ErasedCallable` is constructed, but raw pointers do not survive
precompile serialization, so an instance restored from a precompiled image is
unarmed and throws on use. The owning module must re-arm it once per process
from its `__init__`, typically with a statically-typed `@cfunction`:

    function __init__()
        Libdl.init_callable!(ec, @cfunction(my_impl, Any, ()))
    end

See also [`init_callable!`](@ref).
"""
mutable struct ErasedCallable
    # Invocation goes through this pointer only. It is automatically reset to
    # C_NULL by precompile serialization and re-armed per process via
    # `init_callable!`.
    @atomic ptr::Ptr{Cvoid}
    # GC root for a trampoline created by the generic `init_callable!`
    cf
    # The original callable, for introspection and re-arming
    const callable

    function ErasedCallable(@nospecialize(callable))
        ec = new(C_NULL, nothing, callable)
        init_callable!(ec, callable)
        return ec
    end
end

"""
    init_callable!(ec::ErasedCallable, ptr::Ptr{Cvoid})
    init_callable!(ec::ErasedCallable, callable)

Arm `ec` with a nullary C-callable entry point returning `Any`. The pointer
form is fully static and is what a module's `__init__` should use to re-arm
image-resident instances; the generic form creates a `@cfunction` trampoline
for `callable` at runtime and is what the `ErasedCallable` constructor uses.
"""
function init_callable!(ec::ErasedCallable, ptr::Ptr{Cvoid})
    @atomic :release ec.ptr = ptr
    return ec
end
@noinline function init_callable!(ec::ErasedCallable, @nospecialize(callable))
    cf = @cfunction($callable, Any, ())
    ec.cf = cf # root the trampoline for the lifetime of `ec`
    return init_callable!(ec, Base.unsafe_convert(Ptr{Cvoid}, cf))
end

function (ec::ErasedCallable)()
    ptr = @atomic :acquire ec.ptr
    if ptr == C_NULL
        error("attempt to call an `ErasedCallable` whose pointer was never armed in this process; ",
              "the owning module must re-arm it from its `__init__` via `Libdl.init_callable!`")
    end
    return ccall(ptr, Any, ())
end

"""
    LazyLibraryPath(path_pieces...)

Helper type for lazily constructed library paths for use with [`LazyLibrary`](@ref).
Path pieces are stored unevaluated and joined with `joinpath()` when the library is first
accessed. Each piece must be a string or a nullary [`ErasedCallable`](@ref) returning a
string. Any other object is wrapped in an `ErasedCallable` that lazily calls `string()`
on it, preserving the old piece protocol — but such implicitly-wrapped pieces must be
re-armed per process if they are serialized into a precompiled image.

!!! compat "Julia 1.11"
    `LazyLibraryPath` was added in Julia 1.11.

See also [`LazyLibrary`](@ref), [`BundledLazyLibraryPath`](@ref).

# Examples

```julia
const mylib = LazyLibrary(LazyLibraryPath(artifact_dir, "lib", "libmylib.so.1.2.3"))
```
"""
struct LazyLibraryPath
    pieces::Memory{Union{String, ErasedCallable}}
    function LazyLibraryPath(pieces...)
        mem = Memory{Union{String, ErasedCallable}}(undef, length(pieces))
        for i = 1:length(pieces)
            mem[i] = _lazy_path_piece(pieces[i])
        end
        return new(mem)
    end
end
_lazy_path_piece(p::AbstractString) = String(p)::String
_lazy_path_piece(p::ErasedCallable) = p

# Preserve the old "any object that supports `string()`" piece protocol by
# wrapping unknown pieces in a lazy stringifier
struct PieceStringifier
    x
end
(ps::PieceStringifier)() = string(ps.x)::String
_lazy_path_piece(@nospecialize(p)) = ErasedCallable(PieceStringifier(p))

# Statically-dispatched piece stringification: `string(::LazyLibraryPath)` must
# remain free of dynamic dispatch so that `dlopen(::LazyLibrary)` is compileable
# under `--trim`.
_piece_string(p::String) = p
_piece_string(p::ErasedCallable) = p()::String
Base.string(llp::LazyLibraryPath) = joinpath(String[_piece_string(p) for p in llp.pieces])
Base.cconvert(::Type{Cstring}, llp::LazyLibraryPath) = Base.cconvert(Cstring, string(llp))
# Define `print` so that we can wrap this in a `LazyString`
Base.print(io::IO, llp::LazyLibraryPath) = print(io, string(llp))

# Helper to get `$(private_shlibdir)` at runtime
const private_shlibdir = Base.OncePerProcess{String}() do
    libname = ifelse(isdebugbuild(), "libjulia-internal-debug", "libjulia-internal")
    dirname(dlpath(libname))
end
_bundled_shlibdir() = private_shlibdir()::String
# Shared by every `BundledLazyLibraryPath`; re-armed once per process in
# `Libdl.__init__`, so that stdlib JLLs need no arming code of their own.
const PrivateShlibdirGetter = ErasedCallable(_bundled_shlibdir)

"""
    BundledLazyLibraryPath(subpath)

Helper type for lazily constructed library paths within the Julia distribution.
Constructs paths relative to Julia's private shared library directory.

Primarily used by Julia's standard library. For example:
```julia
const libgmp = LazyLibrary(BundledLazyLibraryPath("libgmp.so.10"))
```

!!! compat "Julia 1.11"
    `BundledLazyLibraryPath` was added in Julia 1.11.

See also [`LazyLibrary`](@ref), [`LazyLibraryPath`](@ref).
"""
BundledLazyLibraryPath(subpath) = LazyLibraryPath(PrivateShlibdirGetter, subpath)

# Small helper struct to initialize a LazyLibrary with its initial set of dependencies
struct InitialDependencies{T}
    dependencies::Vector{T}
end
(init::InitialDependencies)() = copy(init.dependencies)

"""
    LazyLibrary(name; flags = <default dlopen flags>,
                dependencies = LazyLibrary[], on_load_callback = nothing)

Represents a lazily-loaded shared library that delays loading itself and its dependencies
until first use in a `ccall()`, `@ccall`, `dlopen()`, `dlsym()`, `dlpath()`, or `cglobal()`.
This is a thread-safe mechanism for on-demand library initialization.

# Arguments

- `name`: Library name (or lazy path computation) as a `String`,
  [`LazyLibraryPath`](@ref), or [`BundledLazyLibraryPath`](@ref).
- `flags`: Optional `dlopen` flags (default: `RTLD_LAZY | RTLD_DEEPBIND`). See [`dlopen`](@ref).
- `dependencies`: Vector of `LazyLibrary` object references to load before this one.
- `on_load_callback`: Optional function to run arbitrary code on first load (use sparingly,
  as it is not expected that `ccall()` should result in large amounts of Julia code being run.
  You may call `ccall()` from within the `on_load_callback` but only for the current library
  and its dependencies, and user should not call `wait()` on any tasks within the on load
  callback as they may deadlock). The callback is stored as an [`ErasedCallable`](@ref) and
  invoked through its type-erased pointer; if the `LazyLibrary` is serialized into a
  precompiled image, the owning module must re-arm the callback from its `__init__` via
  [`init_callable!`](@ref).

The dlopen operation is thread-safe: only one thread loads the library, acquired after the
release store of the reference to each dependency from loading of each dependency. Other
tasks block until loading completes. The handle is then cached and reused for all subsequent
calls (there is no dlclose for lazy library and dlclose should not be called on the returned handle).

!!! compat "Julia 1.11"
    `LazyLibrary` was added in Julia 1.11.

See also [`LazyLibraryPath`](@ref), [`BundledLazyLibraryPath`](@ref), [`dlopen`](@ref),
[`dlsym`](@ref), [`add_dependency!`](@ref).

# Examples

```julia
# Basic usage
const mylib = LazyLibrary("libmylib")
@ccall mylib.myfunc(42::Cint)::Cint

# With dependencies
const libfoo = LazyLibrary("libfoo")
const libbar = LazyLibrary("libbar"; dependencies=[libfoo])
```

For more examples including platform-specific libraries, lazy path construction, and
migration from `__init__()` patterns, see the manual section on
[Using LazyLibrary for Lazy Loading](@ref man-lazylibrary).
"""
mutable struct LazyLibrary
    # Name and flags to open with
    const path::Union{String, LazyLibraryPath}
    const flags::UInt32

    # Dependencies that must be loaded before we can load
    #
    # The OncePerProcess is introduced here so that any registered dependencies are
    # always ephemeral to a given process (instead of, e.g., persisting depending
    # on whether they were added in the process where this LazyLibrary was created)
    dependencies::Base.OncePerProcess{Vector{LazyLibrary}, InitialDependencies{LazyLibrary}}

    # Callable invoked once upon initial load, through a type-erased pointer so
    # that `dlopen(::LazyLibrary)` stays free of dynamic dispatch. An
    # image-resident callback must be re-armed from the owning module's
    # `__init__` via `init_callable!` (see `ErasedCallable`).
    const on_load_callback::Union{Nothing, ErasedCallable}
    const lock::Base.ReentrantLock

    # Pointer that we eventually fill out upon first `dlopen()`
    @atomic handle::Ptr{Cvoid}
    function LazyLibrary(path; flags = default_rtld_flags, dependencies = LazyLibrary[],
                         on_load_callback = nothing)
        return new(
            _normalize_lazy_path(path),
            UInt32(flags),
            Base.OncePerProcess{Vector{LazyLibrary}}(
                InitialDependencies{LazyLibrary}(dependencies)
            ),
            on_load_callback === nothing ? nothing :
                on_load_callback isa ErasedCallable ? on_load_callback :
                ErasedCallable(on_load_callback),
            Base.ReentrantLock(),
            C_NULL,
        )
    end
end
_normalize_lazy_path(p::AbstractString) = String(p)::String
_normalize_lazy_path(p::LazyLibraryPath) = p
_normalize_lazy_path(@nospecialize(p)) =
    throw(ArgumentError("LazyLibrary path must be an AbstractString or LazyLibraryPath"))

# We support adding dependencies only because of very special situations
# such as LBT needing to have OpenBLAS_jll added as a dependency dynamically.
"""
    add_dependency!(library::LazyLibrary, dependency::LazyLibrary)

Dynamically add a dependency that must be loaded before `library`. Only needed when
dependencies cannot be determined at construction time.

!!! warning
    Dependencies added with this function are **ephemeral** and only persist within the
    current process. They will not persist across precompilation boundaries.

Prefer specifying dependencies in the `LazyLibrary` constructor when possible.

!!! compat "Julia 1.11"
    `add_dependency!` was added in Julia 1.11.

See also [`LazyLibrary`](@ref).
"""
function add_dependency!(ll::LazyLibrary, dep::LazyLibrary)
    @lock ll.lock begin
        push!(ll.dependencies(), dep)
    end
end

# Register `jl_libdl_dlopen_func` so that `ccall()` lowering knows
# how to call `dlopen()`.
Base.unsafe_store!(cglobal(:jl_libdl_dlopen_func, Any), dlopen)

function dlopen(ll::LazyLibrary, flags::Integer = ll.flags; kwargs...)
    handle = @atomic :acquire ll.handle
    if handle == C_NULL
        @lock ll.lock begin
            # Check to see if another thread has already run this
            if ll.handle == C_NULL
                # Ensure that all dependencies are loaded
                for dep in ll.dependencies()
                    dlopen(dep; kwargs...)
                end

                # Load our library
                handle = dlopen(string(ll.path), flags; kwargs...)
                @atomic :release ll.handle = handle

                # Only the thread that loaded the library calls the `on_load_callback()`,
                # through its type-erased pointer (a dynamic call here would make this
                # loader impossible to compile statically, e.g. under `--trim`).
                ol = ll.on_load_callback
                if ol !== nothing
                    ol()
                end
            else
                # Another thread loaded the library while we were waiting
                handle = @atomic :acquire ll.handle
            end
        end
    else
        # Invoke our on load callback, if it exists
        if ll.on_load_callback !== nothing
            # This empty lock protects against the case where we have updated
            # `ll.handle` in the branch above, but not exited the lock.  We want
            # a second thread that comes in at just the wrong time to have to wait
            # for that lock to be released (and thus for the on_load_callback to
            # have finished), hence the empty lock here. But we want the
            # on_load_callback thread to bypass this, which will be happen thanks
            # to the fact that we're using a reentrant lock here.
            @lock ll.lock begin end
        end
    end

    return handle
end
dlopen(x::Any) = throw(TypeError(:dlopen, "", Union{Symbol,String,LazyLibrary}, x))
dlsym(ll::LazyLibrary, args...; kwargs...) = dlsym(dlopen(ll), args...; kwargs...)
dlpath(ll::LazyLibrary) = dlpath(dlopen(ll))

function __init__()
    # `ErasedCallable` pointers are process-local; re-arm the shared
    # private-shlibdir getter used by every `BundledLazyLibraryPath`.
    init_callable!(PrivateShlibdirGetter, @cfunction(_bundled_shlibdir, Any, ()))
    nothing
end
end # module Libdl
