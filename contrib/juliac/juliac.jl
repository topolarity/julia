# This file is a part of Julia. License is MIT: https://julialang.org/license

# Julia compiler wrapper script
# NOTE: The interface and location of this script are considered unstable/experimental

using LazyArtifacts

module JuliaConfig
    include(joinpath(@__DIR__, "..", "julia-config.jl"))
end

julia_cmd = `$(Base.julia_cmd()) --startup-file=no --history-file=no`
cpu_target = get(ENV, "JULIA_CPU_TARGET", nothing)
julia_cmd_target =  `$(Base.julia_cmd(;cpu_target)) --startup-file=no --history-file=no`
output_type = nothing  # exe, sharedlib, sysimage
abi_export_file = nothing
outname = nothing
file = nothing
add_ccallables = false
relative_rpath = false
verbose = false
link_native_libs = String[]  # --link-native=libzstd,libssl,...
foreign_deps_export = nothing  # --export-foreign-deps=path.json

help = findfirst(x->x == "--help", ARGS)
if help !== nothing
    println(
        """
        Usage: julia juliac.jl [--output-exe | --output-lib | --output-sysimage] <name> [options] <file.jl>
        --experimental --trim=<no,safe,unsafe,unsafe-warn>  Only output code statically determined to be reachable
        --export-abi <file>  Emit type / function information for the ABI (in JSON format)
        --compile-ccallable  Include all methods marked `@ccallable` in output
        --relative-rpath     Configure the library / executable to lookup all required libraries in an adjacent "julia/" folder
        --link-native=<comma-separated friendly_names>  Bind ccalls to these libraries via direct external symbols at link time instead of the lazy stub. Names are AbstractSystemLibrary `dlname()` values (e.g. `libzstd` for Zstd_jll).
        --export-foreign-deps=<path>  Write a JSON manifest of every ccall/cglobal usage site to <path>. Includes both native-linked and lazy-stub sites; unknown libs/symbols are flagged with sentinel values.
        --verbose            Request verbose output
        """)
    exit(0)
end

# Copied from PackageCompiler
# https://github.com/JuliaLang/PackageCompiler.jl/blob/1c35331d8ef81494f054bbc71214811253101993/src/PackageCompiler.jl#L147-L190
function get_compiler_cmd(; cplusplus::Bool=false)
    cc = get(ENV, "JULIA_CC", nothing)
    path = nothing
    @static if Sys.iswindows()
        path = joinpath(LazyArtifacts.artifact"mingw-w64",
                        "extracted_files",
                        (Int==Int64 ? "mingw64" : "mingw32"),
                        "bin",
                        cplusplus ? "g++.exe" : "gcc.exe")
        compiler_cmd = `$path`
    end
    if cc !== nothing
        compiler_cmd = Cmd(Base.shell_split(cc))
        path = nothing
    elseif !Sys.iswindows()
        compilers_cpp = ("g++", "clang++")
        compilers_c = ("gcc", "clang")
        found_compiler = false
        if cplusplus
            for compiler in compilers_cpp
                if Sys.which(compiler) !== nothing
                    compiler_cmd = `$compiler`
                    found_compiler = true
                    break
                end
            end
        end
        if !found_compiler
            for compiler in compilers_c
                if Sys.which(compiler) !== nothing
                    compiler_cmd = `$compiler`
                    found_compiler = true
                    if cplusplus && !WARNED_CPP_COMPILER[]
                        @warn "could not find a c++ compiler (g++ or clang++), falling back to $compiler, this might cause link errors"
                        WARNED_CPP_COMPILER[] = true
                    end
                    break
                end
            end
        end
        found_compiler || error("could not find a compiler, looked for ",
            join(((cplusplus ? compilers_cpp : ())..., compilers_c...), ", ", " and "))
    end
    if path !== nothing
        compiler_cmd = addenv(compiler_cmd, "PATH" => string(ENV["PATH"], ";", dirname(path)))
    end
    return compiler_cmd
end

# arguments to forward to julia compilation process
julia_args = []
enable_trim::Bool = false
project::String = "--project=$(Base.active_project())"

let i = 1
    while i <= length(ARGS)
        arg = ARGS[i]
        if arg == "--output-exe" || arg == "--output-lib" || arg == "--output-sysimage"
            isnothing(output_type) || error("Multiple output types specified")
            global output_type = arg
            i == length(ARGS) && error("Output specifier requires an argument")
            global outname = ARGS[i+1]
            i += 1
        elseif arg == "--export-abi"
            i == length(ARGS) && error("Output specifier requires an argument")
            global abi_export_file = ARGS[i+1]
            i += 1
        elseif arg == "--compile-ccallable"
            global add_ccallables = true
        elseif arg == "--verbose"
            global verbose = true
        elseif arg == "--relative-rpath"
            global relative_rpath = true
        elseif startswith(arg, "--trim")
            global enable_trim = arg != "--trim=no"
            push!(julia_args, arg) # forwarded arg
        elseif arg == "--experimental"
            push!(julia_args, arg) # forwarded arg
        elseif startswith(arg, "--link-native=")
            for name in split(arg[length("--link-native=")+1:end], ',', keepempty=false)
                push!(link_native_libs, String(name))
            end
        elseif startswith(arg, "--export-foreign-deps=")
            global foreign_deps_export = arg[length("--export-foreign-deps=")+1:end]
        elseif startswith(arg, "--proj")
            global project = arg
        else
            if arg[1] == '-' || !isnothing(file)
                println("Unexpected argument `$arg`")
                exit(1)
            end
            global file = arg
        end
        i += 1
    end
end

isnothing(outname) && error("No output file specified")
isnothing(file) && error("No input file specified")

function get_rpath(; relative::Bool = false)
    if relative
        if Sys.isapple()
            return "-Wl,-rpath,'@loader_path/julia/' -Wl,-rpath,'@loader_path/'"
        elseif Sys.islinux()
            return "-Wl,-rpath,'\$ORIGIN/julia/' -Wl,-rpath,'\$ORIGIN/'"
        else
            error("unimplemented")
        end
    else
        return JuliaConfig.ldrpath()
    end
end

cc = get_compiler_cmd()
absfile = abspath(file)
cflags = JuliaConfig.cflags(; framework=false)
cflags = Base.shell_split(cflags)
allflags = JuliaConfig.allflags(; framework=false, rpath=false)
allflags = Base.shell_split(allflags)
rpath = get_rpath(; relative = relative_rpath)
rpath = Base.shell_split(rpath)
tmpdir = mktempdir(cleanup=false)
img_path = joinpath(tmpdir, "img.a")
bc_path = joinpath(tmpdir, "img-bc.a")

function precompile_env()
    # Pre-compile the environment
    # (otherwise obscure error messages will occur)
    cmd = addenv(`$julia_cmd $project -e "using Pkg; Pkg.precompile()"`)
    verbose && println("Running: $cmd")
    if !success(pipeline(cmd; stdout, stderr))
        println(stderr, "\nError encountered during pre-compilation of environment.")
        exit(1)
    end
end

function compile_products(enable_trim::Bool)

    # Only strip IR / metadata if not `--trim=no`
    strip_args = String[]
    if enable_trim
        push!(strip_args, "--strip-ir")
        push!(strip_args, "--strip-metadata")
    end

    # Compile the Julia code
    args = String[absfile, output_type, string(add_ccallables)]
    if abi_export_file !== nothing
        push!(args, abi_export_file)
    end
    env = Pair{String,String}["OPENBLAS_NUM_THREADS" => "1", "JULIA_NUM_THREADS" => "1"]
    if !isempty(link_native_libs)
        # Buildscript reads this and registers each name with the runtime
        # native-link table before AOT codegen runs.
        push!(env, "JULIAC_LINK_NATIVE_LIBS" => join(link_native_libs, ','))
    end
    if foreign_deps_export !== nothing
        # Buildscript reads this and forwards to the runtime; the AOT
        # pipeline writes the JSON manifest to this path.
        push!(env, "JULIAC_FOREIGN_DEPS_EXPORT" => abspath(foreign_deps_export))
    end
    cmd = addenv(`$julia_cmd_target $project --output-o $img_path --output-incremental=no $strip_args $julia_args $(joinpath(@__DIR__,"juliac-buildscript.jl")) $(args)`, env...)
    verbose && println("Running: $cmd")
    if !success(pipeline(cmd; stdout, stderr))
        println(stderr, "\nFailed to compile $file")
        exit(1)
    end
end

function link_products()
    global outname
    if output_type == "--output-lib" || output_type == "--output-sysimage"
        of, ext = splitext(outname)
        soext = "." * Base.BinaryPlatforms.platform_dlext()
        if ext == ""
            outname = of * soext
        end
    end

    julia_libs = Base.shell_split(Base.isdebugbuild() ? "-ljulia-debug -ljulia-internal-debug" : "-ljulia -ljulia-internal")
    # Map each `--link-native=<friendly_name>` to a linker arg. Two shapes:
    #   - SONAME-style names containing `.so` or `.a` (e.g. `libopenblas64_.so`,
    #     produced by `Libdl.LazyLibrary`'s default `dlname`) → `-l:<name>`,
    #     which tells GNU ld to match the filename exactly.
    #   - Bare product names (e.g. `libbzip2`, produced by `JLLWrappers.JLLLibrary`)
    #     → `-l<name without leading "lib">`, the standard ld convention.
    # -L paths are the user's responsibility (handled later in the build system).
    native_link_args = String[]
    for name in link_native_libs
        if occursin(".so", name) || endswith(name, ".a")
            push!(native_link_args, "-l:" * name)
        else
            push!(native_link_args, startswith(name, "lib") ? "-l" * name[4:end] : "-l" * name)
        end
    end
    try
        if output_type == "--output-lib"
            cmd2 = `$(cc) $(allflags) $(rpath) -o $outname -shared $(Base.Linking.whole_archive(img_path; is_cc=true)) $(julia_libs) $(native_link_args)`
        elseif output_type == "--output-sysimage"
            cmd2 = `$(cc) $(allflags) $(rpath) -o $outname -shared $(Base.Linking.whole_archive(img_path; is_cc=true)) $(julia_libs) $(native_link_args)`
        else
            cmd2 = `$(cc) $(allflags) $(rpath) -o $outname $(Base.Linking.whole_archive(img_path; is_cc=true)) $(julia_libs) $(native_link_args)`
        end
        verbose && println("Running: $cmd2")
        run(cmd2)
    catch e
        println("\nCompilation failed: ", e)
        exit(1)
    end
end

precompile_env()
compile_products(enable_trim)
link_products()
