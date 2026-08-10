# This file is a part of Julia. License is MIT: https://julialang.org/license

## dummy stub for https://github.com/JuliaBinaryWrappers/CompilerSupportLibraries_jll.jl

baremodule CompilerSupportLibraries_jll
using Base, Libdl, Base.BinaryPlatforms

export libgfortran, libstdcxx, libgomp, libatomic, libgcc_s

# These get calculated in __init__()
const PATH = Ref("")
const PATH_list = String[]
const LIBPATH = Ref("")
const LIBPATH_list = String[]
artifact_dir::String = ""

libatomic_path::String = ""
const libatomic_soname = if Sys.iswindows()
        "libatomic-1.dll"
    elseif Sys.isapple()
        "libatomic.1.dylib"
    elseif Sys.isfreebsd()
        "libatomic.so.3"
    elseif Sys.islinux()
        "libatomic.so.1"
    else
        error("CompilerSupportLibraries_jll: Library 'libatomic' is not available for $(Sys.KERNEL)")
    end
const libatomic = LazyLibrary(
    BundledLazyLibraryPath(libatomic_soname);
    # uuid5(<package uuid>, "libatomic")
    id = Base.UUID("6f70f1a7-e2d5-53ff-bc33-5d3858c96401")
)

if Sys.iswindows() || Sys.isapple() || arch(HostPlatform()) ∈ ("x86_64", "i686")
    global libquadmath_path::String = ""
    const libquadmath_soname = if Sys.iswindows()
            "libquadmath-0.dll"
        elseif Sys.isapple()
            "libquadmath.0.dylib"
        elseif (Sys.islinux() || Sys.isfreebsd()) && arch(HostPlatform()) ∈ ("x86_64", "i686")
            "libquadmath.so.0"
        else
            error("CompilerSupportLibraries_jll: Library 'libquadmath' is not available for $(Sys.KERNEL)")
        end
    const libquadmath = LazyLibrary(
        BundledLazyLibraryPath(libquadmath_soname);
        # uuid5(<package uuid>, "libquadmath")
        id = Base.UUID("4869bb1d-141f-5a01-b337-3d1435fc1f98"),
    )
end

libgcc_s_path::String = ""
const libgcc_s_soname = if Sys.iswindows()
        if arch(HostPlatform()) == "x86_64"
            "libgcc_s_seh-1.dll"
        else
            "libgcc_s_sjlj-1.dll"
        end
    elseif Sys.isapple()
        if arch(HostPlatform()) == "aarch64" || libgfortran_version(HostPlatform()) == v"5"
            "libgcc_s.1.1.dylib"
        else
            "libgcc_s.1.dylib"
        end
    elseif Sys.islinux() || Sys.isfreebsd()
        "libgcc_s.so.1"
    else
        error("CompilerSupportLibraries_jll: Library 'libgcc_s' is not available for $(Sys.KERNEL)")
    end
const libgcc_s = LazyLibrary(
    BundledLazyLibraryPath(libgcc_s_soname);
    # uuid5(<package uuid>, "libgcc_s")
    id = Base.UUID("1cd7433b-ee8f-572a-8a86-1137cb3f5ada")
)

libgfortran_path::String = ""
const libgfortran_soname = if Sys.iswindows()
        string("libgfortran-", libgfortran_version(HostPlatform()).major, ".dll")
    elseif Sys.isapple()
        string("libgfortran.", libgfortran_version(HostPlatform()).major, ".dylib")
    elseif Sys.islinux() || Sys.isfreebsd()
        string("libgfortran.so.", libgfortran_version(HostPlatform()).major)
    else
        error("CompilerSupportLibraries_jll: Library 'libgfortran' is not available for $(Sys.KERNEL)")
    end
const libgfortran = LazyLibrary(
    BundledLazyLibraryPath(libgfortran_soname);
    # uuid5(<package uuid>, "libgfortran")
    id = Base.UUID("77be8d79-76da-57e6-8c3e-8eb4c9c4a43c"),
    dependencies = @static if @isdefined(libquadmath)
        LazyLibrary[libgcc_s, libquadmath]
    else
        LazyLibrary[libgcc_s]
    end
)

libstdcxx_path::String = ""
const libstdcxx_soname = if Sys.iswindows()
        "libstdc++-6.dll"
    elseif Sys.isapple()
        "libstdc++.6.dylib"
    elseif Sys.islinux() || Sys.isfreebsd()
        "libstdc++.so.6"
    else
        error("CompilerSupportLibraries_jll: Library 'libstdcxx' is not available for $(Sys.KERNEL)")
    end
const libstdcxx = LazyLibrary(
    BundledLazyLibraryPath(libstdcxx_soname);
    # uuid5(<package uuid>, "libstdcxx")
    id = Base.UUID("2afcce28-1804-53d7-8eaf-15b85720ac97"),
    dependencies = LazyLibrary[libgcc_s]
)

libgomp_path::String = ""
const libgomp_soname = if Sys.iswindows()
        "libgomp-1.dll"
    elseif Sys.isapple()
        "libgomp.1.dylib"
    elseif Sys.islinux() || Sys.isfreebsd()
        "libgomp.so.1"
    else
        error("CompilerSupportLibraries_jll: Library 'libgomp' is not available for $(Sys.KERNEL)")
    end
const libgomp = LazyLibrary(
    BundledLazyLibraryPath(libgomp_soname);
    # uuid5(<package uuid>, "libgomp")
    id = Base.UUID("d86a9a2a-2317-558f-a0a8-6a2b7a7addd4"),
    dependencies = if Sys.iswindows()
        LazyLibrary[libgcc_s]
    else
        LazyLibrary[]
    end
)

# only define if isfile
let
    if Sys.iswindows() || Sys.isapple() || libc(HostPlatform()) != "musl"
        _libssp_soname = if Sys.iswindows()
            "libssp-0.dll"
        elseif Sys.isapple()
            "libssp.0.dylib"
        elseif Sys.islinux() && libc(HostPlatform()) != "musl"
            "libssp.so.0"
        end
        if isfile(string(BundledLazyLibraryPath(_libssp_soname)))
            global libssp_path::String = ""
            # uuid5(<package uuid>, "libssp")
            @eval const libssp = LazyLibrary(BundledLazyLibraryPath($(_libssp_soname));
                                             id = Base.UUID("558536fb-6a72-5deb-a2f9-856b91bb76ef"))
        end
    end
end

# Conform to LazyJLLWrappers API
function eager_mode()
    dlopen(libatomic)
    dlopen(libgcc_s)
    dlopen(libgomp)
    @static if @isdefined libquadmath
        dlopen(libquadmath)
    end
    @static if @isdefined libssp
        dlopen(libssp)
    end
    dlopen(libgfortran)
    dlopen(libstdcxx)
end
is_available() = true

function __init__()
    global libatomic_path = string(libatomic.path)
    global libgcc_s_path = string(libgcc_s.path)
    global libgomp_path = string(libgomp.path)
    @static if @isdefined libquadmath_path
        global libquadmath_path = string(libquadmath.path)
    end
    @static if @isdefined libssp_path
        global libssp_path = string(libssp.path)
    end
    global libgfortran_path = string(libgfortran.path)
    global libstdcxx_path = string(libstdcxx.path)
    global artifact_dir = dirname(Sys.BINDIR)
    LIBPATH[] = dirname(libgcc_s_path)
    push!(LIBPATH_list, LIBPATH[])
end

if Base.generating_output()
    precompile(eager_mode, ())
    precompile(is_available, ())
end

end  # module CompilerSupportLibraries_jll
