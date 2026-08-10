# This file is a part of Julia. License is MIT: https://julialang.org/license

# Package requirements must survive source loading and pkgimage restoration.

using Test
import Base: PkgId
import UUIDs: UUID

include("tempdepot.jl")

@testset "package implementation rights" begin
    parent = Core.eval(Base.__toplevel__, :(module PackageRightsParent end))
    trigger = Core.eval(Base.__toplevel__, :(module PackageRightsTrigger end))
    extension = Core.eval(Base.__toplevel__, :(module PackageRightsExtension
        module Child end
    end))
    ids = (
        PkgId(UUID("51515151-5151-5151-5151-515151515151"),
              "PackageRightsParent"),
        PkgId(UUID("52525252-5252-5252-5252-525252525252"),
              "PackageRightsTrigger"),
        PkgId(UUID("53535353-5353-5353-5353-535353535353"),
              "PackageRightsExtension"),
    )
    for (root, id) in zip((parent, trigger, extension), ids)
        uuid = convert(NTuple{2,UInt64}, id.uuid)
        ccall(:jl_set_module_uuid, Cvoid, (Any, NTuple{2,UInt64}), root, uuid)
    end

    @lock Base.require_lock begin
        try
            Base.loaded_modules[ids[1]] = parent
            Base.loaded_modules[ids[2]] = trigger
            Base.loaded_modules[ids[3]] = extension
            Base.EXT_PRIMED[ids[3]] = PkgId[ids[1], ids[2]]

            delete!(Base.loaded_modules, ids[2])
            Base._initialize_root_module_implementation_rights!(
                extension, ids[3])
            dormant = Base._root_module_implementation_rights(extension)
            @test Base._packagetype_equiv(
                dormant, Base._packagetype_atom(extension))

            Base.loaded_modules[ids[2]] = trigger
            Base._initialize_root_module_implementation_rights!(
                extension, ids[3])
            intersection = Base._packagetype_meet(
                Base._packagetype_atom(parent),
                Base._packagetype_atom(trigger))
            expected = Base._packagetype_join(
                Base._packagetype_atom(extension), intersection)
            @test Base._packagetype_equiv(
                Base._root_module_implementation_rights(extension), expected)
            @test Base._packagetype_equiv(
                Base._stored_root_module_implementation_rights(
                    extension.Child), expected)
        finally
            delete!(Base.EXT_PRIMED, ids[3])
            for id in ids
                delete!(Base.loaded_modules, id)
            end
        end
    end
end

@testset "package requires graph" begin
    key1 = PkgId(UUID("10101010-1010-1010-1010-101010101010"),
        String(UInt8[0x50, 0x6b, 0x67]))
    key2 = PkgId(UUID("10101010-1010-1010-1010-101010101010"),
        String(UInt8[0x50, 0x6b, 0x67]))
    dep = PkgId(UUID("20202020-2020-2020-2020-202020202020"), "Dep")
    @test key1 === key2
    declared = Base.Compiler.DeclaredPackageGraph{PkgId}([key1 => [dep]])
    @test Base.Compiler.package_graph_has_direct_edge(declared, key2, dep)
    @test Base.Compiler.package_graph_reachable(declared, key2, dep)

    mkdepottempdir() do depot mktempdir() do env
        packages = Dict(
            "PackageGraphA" => "11111111-1111-1111-1111-111111111111",
            "PackageGraphB" => "22222222-2222-2222-2222-222222222222",
            "PackageGraphC" => "33333333-3333-3333-3333-333333333333",
            "PackageGraphD" => "44444444-4444-4444-4444-444444444444",
        )
        package_deps = Dict(
            "PackageGraphA" => ["PackageGraphB", "PackageGraphC", "PackageGraphD"],
            "PackageGraphB" => ["PackageGraphC", "PackageGraphD"],
            "PackageGraphC" => String[],
            "PackageGraphD" => String[],
        )
        sources = Dict(
            "PackageGraphA" => """
                module PackageGraphA
                using PackageGraphB
                const dependency_was_closed = PackageGraphB.closed_during_init[]
                Core._import(PackageGraphA, PackageGraphB.c_module[],
                    :c_value, :value, true)
                end
                """,
            "PackageGraphB" => """
                module PackageGraphB
                using PackageGraphC
                const c_module = Ref{Module}(PackageGraphC)
                const requires_graph_was_open = Ref(false)
                const closed_during_init = Ref(false)
                function __init__()
                    node = Base.LoadedPackageNode(@__MODULE__)
                    requires_graph_was_open[] = Base.requires_graph_node_is_open(node)
                    closed_during_init[] = false
                    try
                        d_module = Base.require(@__MODULE__, :PackageGraphD)
                        Core._using(@__MODULE__, d_module)
                    catch err
                        occursin("the module is closed to new requires edges",
                            sprint(showerror, err)) || rethrow()
                        closed_during_init[] = true
                    end
                    Core._using(@__MODULE__, c_module[])
                end
                end
                """,
            "PackageGraphC" => """
                module PackageGraphC
                export value
                const value = 1
                end
                """,
            "PackageGraphD" => "module PackageGraphD end\n",
        )

        for (name, uuid) in packages
            pkgdir = joinpath(env, name)
            mkpath(joinpath(pkgdir, "src"))
            deps = join(("$depname = \"$(packages[depname])\"" for depname in package_deps[name]), "\n")
            write(joinpath(pkgdir, "Project.toml"), """
                name = "$name"
                uuid = "$uuid"
                version = "1.0.0"
                [deps]
                $deps
                """)
            write(joinpath(pkgdir, "src", "$name.jl"), sources[name])
        end

        project_deps = join(("$name = \"$uuid\"" for (name, uuid) in packages), "\n")
        write(joinpath(env, "Project.toml"), """
            [deps]
            $project_deps
            """)
        manifest_entries = String[]
        for (name, uuid) in packages
            deps = isempty(package_deps[name]) ? "" : "deps = $(repr(package_deps[name]))"
            push!(manifest_entries, """
                [[deps.$name]]
                $deps
                path = "$name"
                uuid = "$uuid"
                version = "1.0.0"
                """)
        end
        write(joinpath(env, "Manifest.toml"), """
            julia_version = "1.14.0"
            manifest_format = "2.0"

            $(join(manifest_entries, "\n"))
            """)

        check_graph = """
            using PackageGraphC
            using PackageGraphA
            a = Base.LoadedPackageNode(PackageGraphA)
            rights = Base._root_module_implementation_rights(PackageGraphA)
            Base._packagetype_equiv(
                rights, Base._packagetype_atom(PackageGraphA)) ||
                error("bad PackageGraphA implementation rights")
            a_requires = Base.direct_package_requires(a)
            sort!(map(node -> Base.PkgId(node).name, a_requires)) ==
                ["PackageGraphB", "PackageGraphC"] || error("bad PackageGraphA edges")
            b = only(node for node in a_requires if Base.PkgId(node).name == "PackageGraphB")
            b_requires = Base.direct_package_requires(b)
            sort!(map(node -> Base.PkgId(node).name, b_requires)) ==
                ["PackageGraphC", "PackageGraphD"] || error("bad PackageGraphB edges")
            c = only(node for node in b_requires if Base.PkgId(node).name == "PackageGraphC")
            Base.Compiler.package_graph_reachable(Base.Compiler.REQUIRES_GRAPH, a, c) ||
                error("transitive package-require reachability failed")
            Base.Compiler.package_graph_node_is_open(Base.Compiler.REQUIRES_GRAPH, a) ||
                error("package requires graph was not open at final runtime")
            PackageGraphA.PackageGraphB.requires_graph_was_open[] ||
                error("requires graph was not open during final-application initialization")
            Core._using(PackageGraphA, PackageGraphA.PackageGraphB)
            using PackageGraphD
            Core._using(PackageGraphA, PackageGraphD)
            sort!(map(node -> Base.PkgId(node).name, Base.direct_package_requires(a))) ==
                ["PackageGraphB", "PackageGraphC", "PackageGraphD"] ||
                error("final-runtime requirement was not recorded")
            """
        load_path = join((env, "@stdlib"), Sys.iswindows() ? ';' : ':')
        modes = (
            (`--compiled-modules=no`, false),
            (`--compiled-modules=yes`, true),
            (`--compiled-modules=existing`, true),
        )
        for (flags, dependency_was_closed) in modes
            check_mode = check_graph * """
                PackageGraphA.dependency_was_closed == $dependency_was_closed ||
                    error("unexpected dependency openness during downstream precompilation")
                """
            cmd = addenv(`$(Base.julia_cmd()) --startup-file=no $flags -e $check_mode`,
                "JULIA_DEPOT_PATH" => depot,
                "JULIA_LOAD_PATH" => load_path,
            )
            @test success(pipeline(cmd; stdout, stderr))
        end
    end end
end
