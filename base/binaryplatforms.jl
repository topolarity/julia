# This file is a part of Julia. License is MIT: https://julialang.org/license

module BinaryPlatforms

export AbstractPlatform, Platform, HostPlatform, platform_dlext, tags, arch, os,
       os_version, libc, libgfortran_version, libstdcxx_version,
       cxxstring_abi, parse_dl_name_version, detect_libgfortran_version,
       detect_libstdcxx_version, detect_cxxstring_abi, call_abi, wordsize, triplet,
       select_platform, platforms_match, platform_name
import .Libc.Libdl
using Base: thisminor, nextpatch, nextminor, nextmajor

### Submodule with information about CPU features
include("cpuid.jl")
using .CPUID

# This exists to ease compatibility with old-style Platform objects
abstract type AbstractPlatform; end

"""
    PlatformAttribute

Defines what a tag key means when a host platform is matched against artifact platforms,
for example by [`select_platform`](@ref).  Every attribute has a `format`, chosen from a
fixed set:

  - `ExactAttribute`: the artifact value must equal the host value (`libc`, `sanitize`, ...)
  - `VersionAttribute`: values are version numbers, and an artifact's version is the lowest
    host version that it supports, up to an optional breaking version (`os_version`,
    `julia_version`, ...); other values (e.g. "none") only match an equal value
  - `ISAAttribute`: values name microarchitectures, and the artifact's instruction set must
    be a subset of the host's (`march`)

An attribute also states what a missing tag means on each side: on an artifact, a missing
tag means the artifact works with `ANY` value unless `artifact_default` names a concrete
value; on a host, a missing tag means the value is `UNKNOWN` unless `host_default` names a
concrete value.  A requirement against an `UNKNOWN` host value is accepted as a weaker
("possible") match.

Base defines attributes for the reserved tags.  Other tags use an `ExactAttribute` with the
default settings, unless the host platform carries an attribute for them, attached with
[`set_attribute!`](@ref) or declared in TOML via `PlatformAttribute(key, dict)`.
"""
abstract type PlatformAttribute end

struct AnyValue end
struct UnknownValue end
const ANY = AnyValue()
const UNKNOWN = UnknownValue()

struct ExactAttribute <: PlatformAttribute
    key::String
    artifact_default::Union{String,AnyValue}
    host_default::Union{String,UnknownValue}
    # Order in which values are preferred when the host value is unknown, best first
    priority::Vector{String}
end
ExactAttribute(key::String; artifact_default=ANY, host_default=UNKNOWN, priority=String[]) =
    ExactAttribute(key, artifact_default, host_default, priority)

struct VersionAttribute <: PlatformAttribute
    key::String
    artifact_default::Union{String,AnyValue}
    host_default::Union{String,UnknownValue}
    # The version component whose increase breaks compatibility: an artifact's version `v`
    # supports the host versions from `v` up to, but excluding, `nextpatch(v)`,
    # `nextminor(v)` or `nextmajor(v)` (`:patch`, `:minor` or `:major`), or any later host
    # version (`nothing`)
    breaking::Union{Symbol,Nothing}
end
function VersionAttribute(key::String; artifact_default=ANY, host_default=UNKNOWN,
                          breaking::Union{Symbol,Nothing}=:patch)
    breaking === nothing || breaking ∈ (:patch, :minor, :major) ||
        throw(ArgumentError("Invalid breaking version component $(repr(breaking))"))
    return VersionAttribute(key, artifact_default, host_default, breaking)
end

struct ISAAttribute <: PlatformAttribute
    key::String
    artifact_default::Union{String,AnyValue}
    host_default::Union{String,UnknownValue}
end
ISAAttribute(key::String; artifact_default=ANY, host_default=UNKNOWN) =
    ISAAttribute(key, artifact_default, host_default)

"""
    Platform

A `Platform` represents all relevant pieces of information that a julia process may need
to know about its execution environment, such as the processor architecture, operating
system, libc implementation, etc...  It is, at its heart, a key-value mapping of tags
(such as `arch`, `os`, `libc`, etc...) to values (such as `"arch" => "x86_64"`, or
`"os" => "windows"`, etc...).  `Platform` objects are extensible in that the tag mapping
is open for users to add their own mappings to, as long as the mappings do not conflict
with the set of reserved tags: `arch`, `os`, `os_version`, `libc`, `call_abi`,
`libgfortran_version`, `libstdcxx_version`, `cxxlib`, `cxxlib_version`,
`cxxstring_abi` and `julia_version`.

Valid tags and values are composed of alphanumeric and period characters.  All tags and
values will be lowercased when stored to reduce variation.

Example:

    Platform("x86_64", "windows"; cuda = "10.1")
"""
struct Platform <: AbstractPlatform
    tags::Dict{String,String}
    # The "compare strategy" allows selective overriding on how a tag is compared
    compare_strategies::Dict{String,Function}
    # Attributes attached to a host platform, which override the built-in ones
    attributes::Dict{String,PlatformAttribute}

    # Passing `tags` as a `Dict` avoids the need to infer different NamedTuple specializations
    function Platform(arch::String, os::String, _tags::Dict{String};
                      validate_strict::Bool = false,
                      compare_strategies::Dict{String,<:Function} = Dict{String,Function}())
        # A wee bit of normalization
        os = lowercase(os)
        arch = CPUID.normalize_arch(arch)

        tags = Dict{String,String}(
            "arch" => arch,
            "os" => os,
        )
        for (tag, value) in _tags
            value = value::Union{String,VersionNumber,Nothing}
            tag = lowercase(tag)
            if tag ∈ ("arch", "os")
                throw(ArgumentError("Cannot double-pass key $(tag)"))
            end

            # Drop `nothing` values; this means feature is not present or use default value.
            if value === nothing
                continue
            end

            add_platform_tag!(tags, tag, value)
        end

        # Auto-map call_abi and libc where necessary:
        if os == "linux" && !haskey(tags, "libc")
            # Default to `glibc` on Linux
            tags["libc"] = "glibc"
        end
        if os == "windows" && !haskey(tags, "libc")
            # Default to `msvcrt` on Windows
            tags["libc"] = "msvcrt"
        end
        if os == "linux" && arch ∈ ("armv7l", "armv6l") && "call_abi" ∉ keys(tags)
            # default `call_abi` to `eabihf` on 32-bit ARM
            tags["call_abi"] = "eabihf"
        end

        # If the user is asking for strict validation, do so.
        if validate_strict
            validate_tags(tags)
        end

        # By default, we compare julia_version only against major and minor versions:
        if haskey(tags, "julia_version") && !haskey(compare_strategies, "julia_version")
            compare_strategies["julia_version"] = compare_julia_version
        end

        return new(tags, compare_strategies, Dict{String,PlatformAttribute}())
    end
end

# Keyword interface (to avoid inference of specialized NamedTuple methods, use the Dict interface for `tags`)
function Platform(arch::String, os::String;
                  validate_strict::Bool = false,
                  compare_strategies::Dict{String,<:Function} = Dict{String,Function}(),
                  kwargs...)
    tags = Dict{String,Any}(String(tag)::String=>tagvalue(value) for (tag, value) in kwargs)
    return Platform(arch, os, tags; validate_strict, compare_strategies)
end

tagvalue(v::Union{String,VersionNumber,Nothing}) = v
tagvalue(v::Symbol) = String(v)
tagvalue(v::AbstractString) = convert(String, v)::String

function add_platform_tag!(tags::Dict{String,String}, tag::String, value::Union{String,VersionNumber,Nothing})
    tag = lowercase(tag)

    # Drop `nothing` values; this means feature is not present or use default value.
    if value === nothing
        return nothing
    end

    # For compatibility, libstdcxx_version counts as both cxxlib=libstdcxx and
    # cxxlib_version, but don't override an explicit existing cxxlib tag (the
    # verifier will check for inconsistencies).
    if tag == "libstdcxx_version"
        haskey(tags, "cxxlib") || add_tag!(tags, "cxxlib", "libstdcxx")
        tag = "cxxlib_version"
    elseif tag == "cxxstring_abi"
        # Implies cxxlib=libstdcxx for compatibility
        haskey(tags, "cxxlib") || add_tag!(tags, "cxxlib", "libstdcxx")
    end

    # Normalize things that are known to be version numbers so that comparisons are easy.
    # Note that in our effort to be extremely compatible, we actually allow something that
    # doesn't parse nicely into a VersionNumber to persist, but if `validate_strict` is
    # set to `true`, it will cause an error later on.
    if tag ∈ ("libgfortran_version", "cxxlib_version", "os_version")
        if isa(value, VersionNumber)
            value = string(value)
        elseif isa(value, String)
            v = tryparse(VersionNumber, value)
            if isa(v, VersionNumber)
                value = string(v)
            end
        end
    elseif tag == "julia_version"
        # Only the major and minor version are meaningful
        v = isa(value, VersionNumber) ? value : tryparse(VersionNumber, value)
        if isa(v, VersionNumber)
            value = string(thisminor(v))
        end
    end

    return add_tag!(tags, tag, string(value)::String)
end

# Simple tag insertion that performs a little bit of validation
function add_tag!(tags::Dict{String,String}, tag::String, value::String)
    # I know we said only alphanumeric and dots, but let's be generous so that we can expand
    # our support in the future while remaining as backwards-compatible as possible.  The
    # only characters that are absolutely disallowed right now are `-`, `+`, ` ` and things
    # that are illegal in filenames:
    nonos = raw"""+- /<>:"'\|?*"""
    if any(occursin(nono, tag) for nono in nonos)
        throw(ArgumentError("Invalid character in tag name \"$(tag)\"!"))
    end

    # Normalize and reject nonos
    value = lowercase(value)
    if any(occursin(nono, value) for nono in nonos)
        throw(ArgumentError("Invalid character in tag value \"$(value)\"!"))
    end
    tags[tag] = value
    return value
end

# Other `Platform` types can override this (I'm looking at you, `AnyPlatform`)
tags(p::Platform) = p.tags

# Make it act more like a dict
Base.getindex(p::AbstractPlatform, k::String) = getindex(tags(p), k)
Base.haskey(p::AbstractPlatform, k::String) = haskey(tags(p), k)
function Base.setindex!(p::AbstractPlatform, v::String, k::String)
    add_platform_tag!(tags(p), k, v)
    return p
end
function Base.setindex!(p::Platform, v::String, k::String)
    add_platform_tag!(tags(p), k, v)
    # Match the constructor, which compares `julia_version` by major and minor version
    if lowercase(k) == "julia_version" && !haskey(p.compare_strategies, "julia_version")
        p.compare_strategies["julia_version"] = compare_julia_version
    end
    return p
end

# Hash definition to ensure that it's stable.  Comparison strategies and attributes only
# describe how a platform is matched, so they do not take part in hashing or equality.
function Base.hash(p::Platform, h::UInt)
    h ⊻= 0x506c6174666f726d % UInt
    h = hash(p.tags, h)
    return h
end

# Simple equality definition; for compatibility testing, use `platforms_match()`
function Base.:(==)(a::Platform, b::Platform)
    return a.tags == b.tags
end


# Allow us to easily serialize Platform objects
function Base.show(io::IO, p::Platform)
    print(io, "Platform(")
    show(io, arch(p))
    print(io, ", ")
    show(io, os(p))
    print(io, "; ")
    # Sort tags so that the output does not depend on `Dict` iteration order
    other_tags = sort!(filter!(kv -> kv[1] ∉ ("arch", "os"), collect(tags(p))); by=first)
    join(io, ("$(k) = $(repr(v))" for (k, v) in other_tags), ", ")
    print(io, ")")
end

# Make showing the platform a bit more palatable
function Base.show(io::IO, ::MIME"text/plain", p::Platform)
    str = string(platform_name(p), " ", arch(p))
    # Add on all the other tags not covered by os/arch:
    other_tags = sort!(filter!(kv -> kv[1] ∉ ("os", "arch"), collect(tags(p))))
    if !isempty(other_tags)
        str = string(str, " {", join([string(k, "=", v) for (k, v) in other_tags], ", "), "}")
    end
    print(io, str)
end

function validate_tags(tags::Dict)
    throw_invalid_key(k) = throw(ArgumentError("Key \"$(k)\" cannot have value \"$(tags[k])\""))
    # Validate `arch`
    if tags["arch"] ∉ ("x86_64", "i686", "armv7l", "armv6l", "aarch64", "powerpc64le", "riscv64")
        throw_invalid_key("arch")
    end
    # Validate `os`
    if tags["os"] ∉ ("linux", "macos", "freebsd", "openbsd", "windows")
        throw_invalid_key("os")
    end
    # Validate `os`/`arch` combination
    throw_os_mismatch() = throw(ArgumentError("Invalid os/arch combination: $(tags["os"])/$(tags["arch"])"))
    if tags["os"] == "windows" && tags["arch"] ∉ ("x86_64", "i686", "armv7l", "aarch64")
        throw_os_mismatch()
    end
    if tags["os"] == "macos" && tags["arch"] ∉ ("x86_64", "aarch64")
        throw_os_mismatch()
    end

    # Validate `os`/`libc` combination
    throw_libc_mismatch() = throw(ArgumentError("Invalid os/libc combination: $(tags["os"])/$(tags["libc"])"))
    if tags["os"] == "linux"
        # Linux always has a `libc` entry
        if tags["libc"] ∉ ("glibc", "musl")
            throw_libc_mismatch()
        end
    elseif tags["os"] == "windows"
        if tags["libc"] ∉ ("msvcrt", "ucrt")
            throw_libc_mismatch()
        end
    else
        # Nothing else is allowed to have a `libc` entry
        if haskey(tags, "libc")
            throw_libc_mismatch()
        end
    end

    # Validate `os`/`arch`/`call_abi` combination
    throw_call_abi_mismatch() = throw(ArgumentError("Invalid os/arch/call_abi combination: $(tags["os"])/$(tags["arch"])/$(tags["call_abi"])"))
    if tags["os"] == "linux" && tags["arch"] ∈ ("armv7l", "armv6l")
        # If an ARM linux does not have `call_abi` set to something valid, be sad.
        if !haskey(tags, "call_abi") || tags["call_abi"] ∉ ("eabihf", "eabi")
            throw_call_abi_mismatch()
        end
    else
        # Nothing else should have a `call_abi`.
        if haskey(tags, "call_abi")
            throw_call_abi_mismatch()
        end
    end

    # Validate `libgfortran_version` is a parsable `VersionNumber`
    throw_version_number(k) = throw(ArgumentError("\"$(k)\" cannot have value \"$(tags[k])\", must be a valid VersionNumber"))
    if "libgfortran_version" in keys(tags) && tryparse(VersionNumber, tags["libgfortran_version"]) === nothing
        throw_version_number("libgfortran_version")
    end

    # Validate `cxxlib` is one of the valid options.
    if haskey(tags, "cxxlib") && tags["cxxlib"] ∉ ("libstdcxx", "libcxx")
        throw_invalid_key("cxxlib")
    end

    # Validate `cxxstring_abi` is one of the two valid options and only used with libstdc++.
    if haskey(tags, "cxxstring_abi") && (tags["cxxstring_abi"] ∉ ("cxx03", "cxx11") || !haskey(tags, "cxxlib") || tags["cxxlib"] != "libstdcxx")
        throw_invalid_key("cxxstring_abi")
    end

    # Validate `cxxlib_version` is a parsable `VersionNumber`
    if haskey(tags, "cxxlib_version") && tryparse(VersionNumber, tags["cxxlib_version"]) === nothing
        throw_version_number("cxxlib_version")
    end
end

function set_compare_strategy!(p::Platform, key::String, f::Function)
    if !haskey(p.tags, key)
        throw(ArgumentError("Cannot set comparison strategy for nonexistent tag $(key)!"))
    end
    p.compare_strategies[key] = f
end

function get_compare_strategy(p::Platform, key::String, default = compare_default)
    if !haskey(p.tags, key)
        throw(ArgumentError("Cannot get comparison strategy for nonexistent tag $(key)!"))
    end
    return get(p.compare_strategies, key, default)
end
get_compare_strategy(p::AbstractPlatform, key::String, default = compare_default) = default



"""
    compare_default(a::String, b::String, a_requested::Bool, b_requested::Bool)

Default comparison strategy that falls back to `a == b`.  This only ever happens if both
`a` and `b` request this strategy, as any other strategy is preferable to this one.
"""
function compare_default(a::String, b::String, a_requested::Bool, b_requested::Bool)
    return a == b
end

"""
    compare_version_cap(a::String, b::String, a_comparator, b_comparator)

Example comparison strategy for `set_comparison_strategy!()` that implements a version
cap for host platforms that support _up to_ a particular version number.  As an example,
if an artifact is built for macOS 10.9, it can run on macOS 10.11, however if it were
built for macOS 10.12, it could not.  Therefore, the host platform of macOS 10.11 has a
version cap at `v"10.11"`.

Note that because both hosts and artifacts are represented with `Platform` objects it
is possible to call `platforms_match()` with two artifacts, a host and an artifact, an
artifact and a host, and even two hosts.  We attempt to do something intelligent for all
cases, but in the case of comparing version caps between two hosts, we return `true` only
if the two host platforms are in fact identical.
"""
function compare_version_cap(a::String, b::String, a_requested::Bool, b_requested::Bool)
    a = VersionNumber(a)
    b = VersionNumber(b)

    # If both b and a requested, then we fall back to equality:
    if a_requested && b_requested
        return a == b
    end

    # Otherwise, do the comparison between the single version cap and the single version:
    if a_requested
        return b <= a
    else
        return a <= b
    end
end

"""
    compare_julia_version(a::String, b::String, a_requested::Bool, b_requested::Bool)

Comparison strategy that every `Platform` with a `julia_version` tag uses: versions match
when their major and minor components are equal.
"""
function compare_julia_version(a::String, b::String, a_requested::Bool, b_requested::Bool)
    a = VersionNumber(a)
    b = VersionNumber(b)
    return a.major == b.major && a.minor == b.minor
end



"""
    HostPlatform(p::AbstractPlatform)

Convert a `Platform` to act like a "host"; e.g. if it has a version-bound tag such as
`"libstdcxx_version" => "3.4.26"`, it will treat that value as an upper bound, rather
than a characteristic.  `Platform` objects that define artifacts generally denote the
SDK or version that the artifact was built with, but for platforms, these versions are
generally the maximal version the platform can support.  The way this transformation
is implemented is to change the appropriate comparison strategies to treat these pieces
of data as bounds rather than points in any comparison.
"""
function HostPlatform(p::AbstractPlatform)
    if haskey(p, "os_version")
        set_compare_strategy!(p, "os_version", compare_version_cap)
    end
    if haskey(p, "cxxlib") && p["cxxlib"] == "libstdcxx" && haskey(p, "cxxlib_version")
        set_compare_strategy!(p, "cxxlib_version", compare_version_cap)
    end
    return p
end

"""
    arch(p::AbstractPlatform)

Get the architecture for the given `Platform` object as a `String`.

# Examples
```jldoctest
julia> arch(Platform("aarch64", "Linux"))
"aarch64"

julia> arch(Platform("amd64", "freebsd"))
"x86_64"
```
"""
arch(p::AbstractPlatform) = get(tags(p), "arch", nothing)

"""
    os(p::AbstractPlatform)

Get the operating system for the given `Platform` object as a `String`.

# Examples
```jldoctest
julia> os(Platform("armv7l", "Linux"))
"linux"

julia> os(Platform("aarch64", "macos"))
"macos"
```
"""
os(p::AbstractPlatform) = get(tags(p), "os", nothing)

# As a special helper, it's sometimes useful to know the current OS at compile-time
function os()
    if Sys.iswindows()
        return "windows"
    elseif Sys.isapple()
        return "macos"
    elseif Sys.isfreebsd()
        return "freebsd"
    elseif Sys.isopenbsd()
        return "openbsd"
    else
        return "linux"
    end
end

"""
    libc(p::AbstractPlatform)

Get the libc for the given `Platform` object as a `String`.  Returns `nothing` on
platforms with no explicit `libc` choices (which is most platforms).

# Examples
```jldoctest
julia> libc(Platform("armv7l", "Linux"))
"glibc"

julia> libc(Platform("aarch64", "linux"; libc="musl"))
"musl"

julia> libc(Platform("i686", "Windows"))
"msvcrt"
```
"""
libc(p::AbstractPlatform) = get(tags(p), "libc", nothing)

"""
    call_abi(p::AbstractPlatform)

Get the call ABI for the given `Platform` object as a `String`.  Returns `nothing` on
platforms with no explicit `call_abi` choices (which is most platforms).

# Examples
```jldoctest
julia> call_abi(Platform("armv7l", "Linux"))
"eabihf"

julia> call_abi(Platform("x86_64", "macos"))
```
"""
call_abi(p::AbstractPlatform) = get(tags(p), "call_abi", nothing)

const platform_names = Dict(
    "linux" => "Linux",
    "macos" => "macOS",
    "windows" => "Windows",
    "freebsd" => "FreeBSD",
    "openbsd" => "OpenBSD",
    nothing => "Unknown",
)

"""
    platform_name(p::AbstractPlatform)

Get the "platform name" of the given platform, returning e.g. "Linux" or "Windows".
"""
function platform_name(p::AbstractPlatform)
    return platform_names[os(p)]
end

function VNorNothing(d::Dict, key)
    v = get(d, key, nothing)
    if v === nothing
        return nothing
    end
    return VersionNumber(v)::VersionNumber
end

"""
    libgfortran_version(p::AbstractPlatform)

Get the libgfortran version dictated by this `Platform` object as a `VersionNumber`,
or `nothing` if no compatibility bound is imposed.
"""
libgfortran_version(p::AbstractPlatform) = VNorNothing(tags(p), "libgfortran_version")

"""
    libstdcxx_version(p::AbstractPlatform)

Get the libstdc++ version dictated by this `Platform` object, or `nothing` if no
compatibility bound is imposed.  This is a compatibility accessor for
`cxxlib = "libstdcxx"` platforms with a `cxxlib_version`.
"""
function libstdcxx_version(p::AbstractPlatform)
    platform_tags = tags(p)
    if haskey(platform_tags, "libstdcxx_version")
        return VNorNothing(platform_tags, "libstdcxx_version")
    end
    if get(platform_tags, "cxxlib", nothing) == "libstdcxx"
        return VNorNothing(platform_tags, "cxxlib_version")
    end
    return nothing
end

"""
    cxxstring_abi(p::AbstractPlatform)

Get the c++ string ABI dictated by this `Platform` object, or `nothing` if no ABI is imposed.
"""
cxxstring_abi(p::AbstractPlatform) = get(tags(p), "cxxstring_abi", nothing)

"""
    os_version(p::AbstractPlatform)

Get the OS version dictated by this `Platform` object, or `nothing` if no OS version is
imposed/no data is available.  This is most commonly used by MacOS and FreeBSD objects
where we have high platform SDK fragmentation, and features are available only on certain
platform versions.
"""
os_version(p::AbstractPlatform) = VNorNothing(tags(p), "os_version")

"""
    wordsize(p::AbstractPlatform)

Get the word size for the given `Platform` object.

# Examples
```jldoctest
julia> wordsize(Platform("armv7l", "linux"))
32

julia> wordsize(Platform("x86_64", "macos"))
64
```
"""
wordsize(p::AbstractPlatform) = (arch(p) ∈ ("i686", "armv6l", "armv7l")) ? 32 : 64

"""
    triplet(p::AbstractPlatform)

Get the target triplet for the given `Platform` object as a `String`.

# Examples
```jldoctest
julia> triplet(Platform("x86_64", "MacOS"))
"x86_64-apple-darwin"

julia> triplet(Platform("i686", "Windows"))
"i686-w64-mingw32"

julia> triplet(Platform("armv7l", "Linux"; libgfortran_version="3"))
"armv7l-linux-gnueabihf-libgfortran3"
```
"""
function triplet(p::AbstractPlatform)
    str = string(
        arch(p)::Union{Symbol,String},
        os_str(p),
        libc_str(p),
        call_abi_str(p),
    )

    # Tack on optional compiler ABI flags
    libgfortran_version_ = libgfortran_version(p)
    if libgfortran_version_ !== nothing
        str = string(str, "-libgfortran", libgfortran_version_.major)
    end
    cxxstring_abi_ = cxxstring_abi(p)
    if cxxstring_abi_ !== nothing
        str = string(str, "-", cxxstring_abi_)
    end
    libstdcxx_version_ = libstdcxx_version(p)
    if libstdcxx_version_ !== nothing
        str = string(str, "-libstdcxx", libstdcxx_version_.patch)
    end

    # Tack on all extra tags, sorted so that the output does not depend on `Dict` iteration order
    for (tag, val) in sort!(collect(tags(p)); by=first)
        if tag ∈ ("os", "arch", "libc", "call_abi", "libgfortran_version", "libstdcxx_version", "cxxstring_abi", "os_version")
            continue
        end
        if tag == "cxxlib" && val == "libstdcxx" && (cxxstring_abi_ !== nothing || libstdcxx_version_ !== nothing)
            # Implied by above
            continue
        end
        if tag == "cxxlib_version" && get(tags(p), "cxxlib", nothing) == "libstdcxx"
            # Emitted as a libstdcxx compatibility tag above
            continue
        end
        str = string(str, "-", tag, "+", val)
    end
    return str
end

function os_str(p::AbstractPlatform)
    if os(p) == "linux"
        return "-linux"
    elseif os(p) == "macos"
        osvn = os_version(p)
        if osvn !== nothing
            return "-apple-darwin$(osvn.major)"
        else
            return "-apple-darwin"
        end
    elseif os(p) == "windows"
        return "-w64"
    elseif os(p) == "freebsd"
        osvn = os_version(p)
        if osvn !== nothing
            return "-unknown-freebsd$(osvn.major).$(osvn.minor)"
        else
            return "-unknown-freebsd"
        end
    elseif os(p) == "openbsd"
        return "-unknown-openbsd"
    else
        return "-unknown"
    end
end

# Helper functions for Linux and FreeBSD libc/abi mishmashes
function libc_str(p::AbstractPlatform)
    lc = libc(p)
    if lc === nothing
        return ""
    elseif lc === "glibc"
        return "-gnu"
    elseif lc === "msvcrt"
        return "-mingw32"
    elseif lc === "ucrt"
        return "-ucrt-mingw32"
    else
        return string("-", lc)
    end
end
function call_abi_str(p::AbstractPlatform)
    cabi = call_abi(p)
    cabi === nothing ? "" : string(cabi::Union{Symbol,String})
end

Sys.isapple(p::AbstractPlatform) = os(p) == "macos"
Sys.islinux(p::AbstractPlatform) = os(p) == "linux"
Sys.iswindows(p::AbstractPlatform) = os(p) == "windows"
Sys.isfreebsd(p::AbstractPlatform) = os(p) == "freebsd"
Sys.isopenbsd(p::AbstractPlatform) = os(p) == "openbsd"
Sys.isbsd(p::AbstractPlatform) = os(p) ∈ ("freebsd", "openbsd", "macos")
Sys.isunix(p::AbstractPlatform) = Sys.isbsd(p) || Sys.islinux(p)

const arch_mapping = Dict(
    "x86_64" => "(x86_|amd)64",
    "i686" => "i\\d86",
    "aarch64" => "(aarch64|arm64)",
    "armv7l" => "arm(v7l)?", # if we just see `arm-linux-gnueabihf`, we assume it's `armv7l`
    "armv6l" => "armv6l",
    "powerpc64le" => "p(ower)?pc64le",
    "riscv64" => "(rv64|riscv64)",
)
# Keep this in sync with `CPUID.ISAs_by_family`
# These are the CPUID side of the microarchitectures targeted by GCC flags in BinaryBuilder.jl
const arch_march_isa_mapping = let
    function get_set(arch, name)
        all = CPUID.ISAs_by_family[arch]
        return all[findfirst(x -> x.first == name, all)].second
    end
    Dict(
        "i686" => [
            "pentium4" => get_set("i686", "pentium4"),
            "prescott" => get_set("i686", "prescott"),
        ],
        "x86_64" => [
            "x86_64" => get_set("x86_64", "x86_64"),
            "avx" => get_set("x86_64", "sandybridge"),
            "avx2" => get_set("x86_64", "haswell"),
            "avx512" => get_set("x86_64", "skylake_avx512"),
        ],
        "aarch64" => [
            "armv8_0" => get_set("aarch64", "armv8.0-a"),
            "armv8_1" => get_set("aarch64", "armv8.1-a"),
            "armv8_2_crypto" => get_set("aarch64", "armv8.2-a+crypto"),
            "a64fx" => get_set("aarch64", "a64fx"),
            "apple_m1" => get_set("aarch64", "apple_m1"),
        ],
        "riscv64" => [
            "riscv64" => get_set("riscv64", "riscv64"),
        ],
    )
end
const os_mapping = Dict(
    "macos" => "-apple-darwin[\\d\\.]*",
    "freebsd" => "-(.*-)?freebsd[\\d\\.]*",
    "openbsd" => "-(.*-)?openbsd[\\d\\.]*",
    "windows" => "-w64",
    "linux" => "-(.*-)?linux",
)
const libc_mapping = Dict(
    "libc_nothing" => "",
    "ucrt"  => "-ucrt-mingw32",
    "msvcrt" => "-mingw32", # We default to msvcrt for plain -mingw32 on Windows
    "glibc" => "-gnu",
    "musl" => "-musl",
)
const call_abi_mapping = Dict(
    "call_abi_nothing" => "",
    "eabihf" => "eabihf",
    "eabi" => "eabi",
)
const libgfortran_version_mapping = Dict(
    "libgfortran_nothing" => "",
    "libgfortran3" => "(-libgfortran3)|(-gcc4)", # support old-style `gccX` versioning
    "libgfortran4" => "(-libgfortran4)|(-gcc7)",
    "libgfortran5" => "(-libgfortran5)|(-gcc8)",
)
const cxxstring_abi_mapping = Dict(
    "cxxstring_nothing" => "",
    "cxx03" => "-cxx03",
    "cxx11" => "-cxx11",
)
const libstdcxx_version_mapping = Dict{String,String}(
    "libstdcxx_nothing" => "",
    "libstdcxx" => "-libstdcxx\\d+",
)

const triplet_regex = let
    # Helper function to collapse dictionary of mappings down into a regex of
    # named capture groups joined by "|" operators
    c(mapping) = string("(",join(["(?<$k>$v)" for (k, v) in mapping], "|"), ")")

    Regex(string(
        "^",
        # First, the core triplet; arch/os/libc/call_abi
        c(arch_mapping),
        c(os_mapping),
        c(libc_mapping),
        c(call_abi_mapping),
        # Next, optional things, like libgfortran/libstdcxx/cxxstring abi
        c(libgfortran_version_mapping),
        c(cxxstring_abi_mapping),
        c(libstdcxx_version_mapping),
        # Finally, the catch-all for extended tags
        "(?<tags>(?:-[^-]+\\+[^-]+)*)?",
        "\$",
    ))
end

"""
    parse(::Type{Platform}, triplet::AbstractString)

Parses a string platform triplet back into a `Platform` object.
"""
function Base.parse(::Type{Platform}, triplet::String; validate_strict::Bool = false)
    m = match(triplet_regex, triplet)
    if m !== nothing
        # Helper function to find the single named field within the giant regex
        # that is not `nothing` for each mapping we give it.
        get_field(m, mapping) = begin
            for k in keys(mapping)
                if m[k] !== nothing
                    # Convert our sentinel `nothing` values to actual `nothing`
                    if endswith(k, "_nothing")
                        return nothing
                    end
                    # Convert libgfortran/libstdcxx version numbers
                    if startswith(k, "libgfortran")
                        return VersionNumber(parse(Int,k[12:end]))
                    elseif startswith(k, "libstdcxx")
                        return VersionNumber(3, 4, parse(Int,m[k][11:end]))
                    else
                        return k
                    end
                end
            end
        end

        # Extract the information we're interested in:
        tags = Dict{String,Any}()
        arch = get_field(m, arch_mapping)
        os = get_field(m, os_mapping)
        tags["libc"] = get_field(m, libc_mapping)
        tags["call_abi"] = get_field(m, call_abi_mapping)
        tags["libgfortran_version"] = get_field(m, libgfortran_version_mapping)
        tags["libstdcxx_version"] = get_field(m, libstdcxx_version_mapping)
        tags["cxxstring_abi"] = get_field(m, cxxstring_abi_mapping)
        function split_tags(tagstr)
            tag_fields = split(tagstr, "-"; keepempty=false)
            if isempty(tag_fields)
                return Pair{String,String}[]
            end
            return map(v -> String(v[1]) => String(v[2]), split.(tag_fields, "+"))
        end
        merge!(tags, Dict(split_tags(m["tags"])))

        # Special parsing of os version number, if any exists
        function extract_os_version(os_name, pattern)
            m_osvn = match(pattern, m[os_name])
            if m_osvn !== nothing
                return VersionNumber(m_osvn.captures[1])
            end
            return nothing
        end
        os_version = nothing
        if os == "macos"
            os_version = extract_os_version("macos", r".*darwin([\d.]+)"sa)
        end
        if os == "freebsd"
            os_version = extract_os_version("freebsd", r".*freebsd([\d.]+)"sa)
        end
        if os == "openbsd"
            os_version = extract_os_version("openbsd", r".*openbsd([\d.]+)"sa)
        end
        tags["os_version"] = os_version

        return Platform(arch, os, tags; validate_strict)
    end
    throw(ArgumentError("Platform `$(triplet)` is not an officially supported platform"))
end
Base.parse(::Type{Platform}, triplet::AbstractString; kwargs...) =
    parse(Platform, convert(String, triplet)::String; kwargs...)

function Base.tryparse(::Type{Platform}, triplet::AbstractString)
    try
        parse(Platform, triplet)
    catch e
        if isa(e, InterruptException)
            rethrow(e)
        end
        return nothing
    end
end

"""
    platform_dlext(p::AbstractPlatform = HostPlatform())

Return the dynamic library extension for the given platform, defaulting to the
currently running platform.  E.g. returns "so" for a Linux-based platform,
"dll" for a Windows-based platform, etc...
"""
function platform_dlext(p::AbstractPlatform = HostPlatform())
    if os(p) == "windows"
        return "dll"
    elseif os(p) == "macos"
        return "dylib"
    else
        return "so"
    end
end

# Not general purpose, just for parse_dl_name_version
function _this_os_name()
    if Sys.iswindows()
        return "windows"
    elseif Sys.isapple()
        return "macos"
    else
        return "other"
    end
end

"""
    parse_dl_name_version(path::String, platform::AbstractPlatform)

Given a path to a dynamic library, parse out what information we can
from the filename.  E.g. given something like "lib/libfoo.so.3.2",
this function returns `"libfoo", v"3.2"`.  If the path name is not a
valid dynamic library, this method throws an error.  If no soversion
can be extracted from the filename, as in "libbar.so" this method
returns `"libbar", nothing`.

A soversion may carry a trailing tag, as Julia's own LLVM does; the tag is not part of the
name and is not reported.

# Examples
```jldoctest
julia> parse_dl_name_version("lib/libfoo.so.3.2", "linux")
("libfoo", v"3.2.0")

julia> parse_dl_name_version("libbar.so", "linux")
("libbar", nothing)

julia> parse_dl_name_version("libLLVM.so.21.1jl", "linux")
("libLLVM", v"21.1.0")
```
"""
function parse_dl_name_version(path::String, os::String=_this_os_name())
    # Use an extraction regex that matches the given OS
    # A tag may follow the soversion (`libLLVM.so.21.1jl`), but only after a version.
    local dlregex
    # Keep this up to date with _this_os_name
    if os == "windows"
        # On Windows, libraries look like `libnettle-6.dll`.
        # Stay case-insensitive, the suffix might be `.DLL`.
        dlregex = r"^(.*?)(?:-(?:((?:[\.\d]+)+)([A-Za-z][\w\.]*)?)?)?\.dll$"isa
    elseif os == "macos"
        # On OSX, libraries look like `libnettle.6.3.dylib`
        dlregex = r"^(.*?)(?:((?:\.[\d]+)+)([A-Za-z][\w\-]*)?)?\.dylib$"sa
    else
        # On Linux and other BSDs, libraries look like `libnettle.so.6.3.0`
        dlregex = r"^(.*?)\.so(?:((?:\.[\d]+)+)([A-Za-z][\w\-]*)?)?$"sa
    end

    m = match(dlregex, basename(path))
    if m === nothing
        throw(ArgumentError("Invalid dynamic library path '$path'"))
    end

    # Extract name and version
    name = m.captures[1]
    version = m.captures[2]
    if version === nothing || isempty(version)
        version = nothing
    else
        version = VersionNumber(strip(version, '.'))
    end
    return name, version
end

# Adapter for `AbstractString`
function parse_dl_name_version(path::AbstractString, os::AbstractString=_this_os_name())
    return parse_dl_name_version(string(path)::String, string(os)::String)
end

function get_csl_member(member::Symbol)
    # If CompilerSupportLibraries_jll is a stdlib, we can just grab things from it
    csl_pkgids = filter(pkgid -> pkgid.name == "CompilerSupportLibraries_jll", keys(Base.loaded_modules))
    if !isempty(csl_pkgids)
        CSL_mod = Base.loaded_modules[first(csl_pkgids)]

        # This can fail during bootstrap, so we skip in that case.
        if isdefined(CSL_mod, member)
            return getproperty(CSL_mod, member)
        end
    end

    return nothing
end


function _get_libgfortran_path()
    # If CompilerSupportLibraries_jll is a stdlib, we can just directly ask for
    # the path here, without checking `dllist()`:
    libgfortran_path = get_csl_member(:libgfortran_path)
    if libgfortran_path !== nothing
        return libgfortran_path::String
    end

    # Otherwise, look for it having already been loaded by something
    libgfortran_paths = filter!(x -> occursin("libgfortran", x), Libdl.dllist())
    if !isempty(libgfortran_paths)
        return first(libgfortran_paths)::String
    end

    # One day, I hope to not be linking against libgfortran in base Julia
    return nothing
end

function _get_libstdcxx_handle()
    # If CompilerSupportLibraries_jll is a stdlib, we can just directly open it
    libstdcxx = get_csl_member(:libstdcxx)
    if libstdcxx !== nothing
        return nothing
    end

    # Otherwise, look for it having already been loaded by something
    libstdcxx_paths = filter!(x -> occursin("libstdc++", x), Libdl.dllist())
    if !isempty(libstdcxx_paths)
        return Libdl.dlopen(first(libstdcxx_paths), Libdl.RTLD_NOLOAD)::Ptr{Cvoid}
    end

    # One day, I hope to not be linking against libstdc++ in base Julia
    return nothing
end

"""
    detect_libgfortran_version()

Inspects the current Julia process to determine the libgfortran version this Julia is
linked against (if any).  Returns `nothing` if no libgfortran version dependence is
detected.
"""
function detect_libgfortran_version()
    libgfortran_path = _get_libgfortran_path()
    _, version = parse_dl_name_version(libgfortran_path, os())
    if version === nothing
        # Even though we complain about this, we allow it to continue in the hopes that
        # we shall march on to a BRIGHTER TOMORROW.  One in which we are not shackled
        # by the constraints of libgfortran compiler ABIs upon our precious programming
        # languages; one where the mistakes of yesterday are mere memories and not
        # continual maintenance burdens upon the children of the dawn; one where numeric
        # code may be cleanly implemented in a modern language and not bestowed onto the
        # next generation by grizzled ancients, documented only with a faded yellow
        # sticky note that bears a hastily-scribbled "good luck".
        @warn("Unable to determine libgfortran version from '$(libgfortran_path)'")
    end
    return version
end

"""
    detect_libstdcxx_version(max_minor_version::Int=30)

Inspects the currently running Julia process to find out what version of libstdc++
it is linked against (if any).  `max_minor_version` is the latest version in the
3.4 series of GLIBCXX where the search is performed.
"""
function detect_libstdcxx_version(max_minor_version::Int=30)
    # Brute-force our way through GLIBCXX_* symbols to discover which version we're linked against
    libstdcxx = _get_libstdcxx_handle()

    if libstdcxx !== nothing
        # Try all GLIBCXX versions down to GCC v4.8:
        # https://gcc.gnu.org/onlinedocs/libstdc++/manual/abi.html
        for minor_version in max_minor_version:-1:18
            if Libdl.dlsym(libstdcxx, "GLIBCXX_3.4.$(minor_version)"; throw_error=false) !== nothing
                return VersionNumber("3.4.$(minor_version)")
            end
        end
    end
    return nothing
end

"""
    detect_cxxstring_abi()

Inspects the currently running Julia process to see what version of the C++11 string ABI
it was compiled with (this is only relevant if compiled with `g++`; `clang` has no
incompatibilities yet, bless its heart).  In reality, this actually checks for symbols
within LLVM, but that is close enough for our purposes, as you can't mix configurations
between Julia and LLVM; they must match.
"""
function detect_cxxstring_abi()
    # First, if we're not linked against libstdc++, then early-exit because this doesn't matter.
    libstdcxx_paths = filter!(x -> occursin("libstdc++", x), Libdl.dllist())
    if isempty(libstdcxx_paths)
        # We were probably built by `clang`; we don't link against `libstdc++`` at all.
        return nothing
    end

    function open_libllvm(f::Function)
        for lib_name in (Base.libllvm_name, "libLLVM", "LLVM", "libLLVMSupport")
            hdl = Libdl.dlopen_e(lib_name)
            if hdl != C_NULL
                try
                    return f(hdl)
                finally
                    Libdl.dlclose(hdl)
                end
            end
        end
        error("Unable to open libLLVM!")
    end

    return open_libllvm() do hdl
        # Check for llvm::sys::getProcessTriple(), first without cxx11 tag:
        if Libdl.dlsym_e(hdl, "_ZN4llvm3sys16getProcessTripleEv") != C_NULL
            return "cxx03"
        elseif Libdl.dlsym_e(hdl, "_ZN4llvm3sys16getProcessTripleB5cxx11Ev") != C_NULL
            return "cxx11"
        else
            @warn("Unable to find llvm::sys::getProcessTriple() in libLLVM!")
            return nothing
        end
    end
end

"""
    host_triplet(build_triplet::String = Base.BUILD_TRIPLET, ext_tags::String = Base.BUILD_EXT_TAGS)

Build host triplet out of `Sys.MACHINE` and various introspective utilities that
detect compiler ABI values such as `libgfortran_version`, `libstdcxx_version` and
`cxxstring_abi`.  We do this without using any `Platform` tech as it must run before
we have much of that built.  Extended tags recorded by the build (e.g. `-sanitize+address`)
are appended after the compiler ABI tags, as the triplet grammar requires.
"""
function host_triplet(build_triplet::String = Base.BUILD_TRIPLET, ext_tags::String = Base.BUILD_EXT_TAGS)
    str = build_triplet

    if !occursin("-libgfortran", str)
        libgfortran_version = detect_libgfortran_version()
        if libgfortran_version !== nothing
            str = string(str, "-libgfortran", libgfortran_version.major)
        end
    end

    if !occursin("-cxx", str)
        cxxstring_abi = detect_cxxstring_abi()
        if cxxstring_abi !== nothing
            str = string(str, "-", cxxstring_abi)
        end
    end

    if !occursin("-libstdcxx", str)
        libstdcxx_version = detect_libstdcxx_version()
        if libstdcxx_version !== nothing
            str = string(str, "-libstdcxx", libstdcxx_version.patch)
        end
    end

    # Add on any extended tags recorded by the build
    str = string(str, ext_tags)

    # Add on julia_version extended tag
    if !occursin("-julia_version+", str)
        str = string(str, "-julia_version+", VersionNumber(VERSION.major, VERSION.minor, VERSION.patch))
    end
    return str
end

"""
    HostPlatform()

Return the `Platform` object that corresponds to the current host system, with all
relevant comparison strategies set to host platform mode.  This is equivalent to:

    HostPlatform(parse(Platform, Base.BinaryPlatforms.host_triplet()))
"""
function HostPlatform()
    return HostPlatform(parse(Platform, host_triplet()))::Platform
end

## Platform attributes: matching a host against artifacts

# Attributes of the reserved tags.  Any other tag uses `ExactAttribute(key)`, unless the
# host carries an attribute for it.
const builtin_attributes = Dict{String,PlatformAttribute}(
    "arch" => ExactAttribute("arch"),
    "os" => ExactAttribute("os"),
    "libc" => ExactAttribute("libc"),
    "call_abi" => ExactAttribute("call_abi"),
    # Instrumented and uninstrumented binaries cannot be mixed; a platform without a
    # `sanitize` tag is known to be uninstrumented.
    "sanitize" => ExactAttribute("sanitize"; artifact_default="none", host_default="none"),
    "cxxlib" => ExactAttribute("cxxlib"),
    "cxxstring_abi" => ExactAttribute("cxxstring_abi"; priority=["cxx11", "cxx03"]),
    "cxxlib_version" => VersionAttribute("cxxlib_version"; breaking=nothing),
    "libgfortran_version" => VersionAttribute("libgfortran_version"; breaking=:major),
    "os_version" => VersionAttribute("os_version"; breaking=nothing),
    "julia_version" => VersionAttribute("julia_version"; breaking=:minor),
    "march" => ISAAttribute("march"),
)

# Order in which keys break remaining ties between equally good matches.  Keys that are not
# listed come afterwards, sorted by name.
const attribute_priority = ("arch", "os", "libc", "call_abi", "sanitize", "cxxlib",
                            "cxxstring_abi", "libgfortran_version", "cxxlib_version",
                            "os_version", "julia_version", "march")

"""
    set_attribute!(p::Platform, attr::PlatformAttribute)

Attach `attr` to the host platform `p`, so that matching `p` against artifact platforms
interprets the tag `attr.key` according to `attr`.  This overrides the built-in attribute
of a reserved tag, as well as any comparison strategy set for the same key.  Platform
augmentation hooks call this for the tags that they add.
"""
function set_attribute!(p::Platform, attr::PlatformAttribute)
    p.attributes[attribute_key(attr)] = attr
    return p
end

attribute_key(attr::PlatformAttribute) = with_format(a -> a.key, attr)::String

function Base.:(==)(a::T, b::T) where {T<:PlatformAttribute}
    return all(f -> getfield(a, f) == getfield(b, f), fieldnames(T))
end
function Base.hash(a::PlatformAttribute, h::UInt)
    h = hash(typeof(a), h)
    for f in fieldnames(typeof(a))
        h = hash(getfield(a, f), h)
    end
    return h
end

"""
    PlatformAttribute(key::String, declaration::AbstractDict)

Construct the attribute of tag `key` from a declaration, such as a TOML table:

```toml
format = "version"     # "exact" (default), "version" or "isa"
breaking = "major"     # "version" only: "patch" (default), "minor", "major" or "none"
priority = ["a", "b"]  # "exact" only: values to prefer, best first
artifact_default = "x" # value of a missing artifact tag (default: any value)
host_default = "x"     # value of a missing host tag (default: unknown)
```
"""
function PlatformAttribute(key::String, d::AbstractDict)
    strvec(v) = String[lowercase(string(x)) for x in v]
    key = lowercase(key)
    format = lowercase(string(get(d, "format", "exact")))
    artifact_default = haskey(d, "artifact_default") ? lowercase(string(d["artifact_default"])) : ANY
    host_default = haskey(d, "host_default") ? lowercase(string(d["host_default"])) : UNKNOWN
    if format == "exact"
        return ExactAttribute(key; artifact_default, host_default,
                              priority=strvec(get(d, "priority", String[])))
    elseif format == "version"
        b = lowercase(string(get(d, "breaking", "patch")))
        breaking = b == "none" ? nothing : Symbol(b)
        return VersionAttribute(key; artifact_default, host_default, breaking)
    elseif format == "isa"
        return ISAAttribute(key; artifact_default, host_default)
    end
    throw(ArgumentError("Unknown platform attribute format $(repr(format)) for tag $(repr(key))"))
end

# The formats are a closed set: split on them explicitly, so that matching does not need
# dynamic dispatch.
@inline function with_format(f, attr::PlatformAttribute)
    if attr isa ExactAttribute
        return f(attr)
    elseif attr isa VersionAttribute
        return f(attr)
    elseif attr isa ISAAttribute
        return f(attr)
    end
    throw(ArgumentError("Unsupported platform attribute type $(typeof(attr))"))
end

"""
    parse_value(attr::PlatformAttribute, value::String, p::AbstractPlatform)

Parse the tag `value` carried by platform `p` into the representation that `attr`
compares, or return `nothing` if it does not parse.  `p` provides context, such as the
architecture that a microarchitecture name refers to.
"""
parse_value(::ExactAttribute, s::String, ::AbstractPlatform) = s
parse_value(::VersionAttribute, s::String, ::AbstractPlatform) = tryparse(VersionNumber, s)
function parse_value(::ISAAttribute, s::String, p::AbstractPlatform)
    isas = get(arch_march_isa_mapping, arch(p), nothing)
    if isas !== nothing
        idx = findfirst(x -> x.first == s, isas)
        idx === nothing || return isas[idx].second
    end
    # Microarchitectures without a known instruction set are compared by name
    return s
end

# Whether the parsed requirement `req` is satisfied by the parsed host value `have`
satisfies_value(::ExactAttribute, req::String, have::String) = req == have
function satisfies_value(attr::VersionAttribute, req::VersionNumber, have::VersionNumber)
    req <= have || return false
    b = attr.breaking
    return b === nothing || have < (b === :patch ? nextpatch(req) :
                                    b === :minor ? nextminor(req) : nextmajor(req))
end
satisfies_value(::ISAAttribute, req::CPUID.ISA, have::CPUID.ISA) = req <= have
satisfies_value(::ISAAttribute, req::String, have::String) = req == have
satisfies_value(::ISAAttribute, req, have) = false

# Results of comparing two candidates on one key
const PREFER_FIRST = Int8(1)
const PREFER_SECOND = Int8(-1)
const PREFER_NEITHER = Int8(0)
const INCOMPARABLE = Int8(2)

# How the parsed requirements `a` and `b`, which both match, rank against each other,
# depending on whether the host value is unknown
function prefer_value(attr::ExactAttribute, a::String, b::String, host_unknown::Bool)
    a == b && return PREFER_NEITHER
    ia = something(findfirst(==(a), attr.priority), typemax(Int))
    ib = something(findfirst(==(b), attr.priority), typemax(Int))
    return ia < ib ? PREFER_FIRST : ia > ib ? PREFER_SECOND : INCOMPARABLE
end
prefer_value(::VersionAttribute, a::VersionNumber, b::VersionNumber, host_unknown::Bool) =
    a > b ? PREFER_FIRST : a < b ? PREFER_SECOND : PREFER_NEITHER
function prefer_value(::ISAAttribute, a::CPUID.ISA, b::CPUID.ISA, host_unknown::Bool)
    a <= b && b <= a && return PREFER_NEITHER
    if host_unknown
        # The host's instruction set is unknown: prefer the least demanding build
        a < b && return PREFER_FIRST
        b < a && return PREFER_SECOND
    else
        # Prefer the most specific build that the host supports
        b < a && return PREFER_FIRST
        a < b && return PREFER_SECOND
    end
    return INCOMPARABLE
end
prefer_value(::ISAAttribute, a::String, b::String, host_unknown::Bool) = a == b ? PREFER_NEITHER : INCOMPARABLE
prefer_value(::ISAAttribute, a, b, host_unknown::Bool) = INCOMPARABLE

# Quality of a match, combined across keys by taking the minimum
const NO_MATCH = Int8(0)
const POSSIBLE_MATCH = Int8(1)  # depends on host values that are unknown
const CERTAIN_MATCH = Int8(2)

function requirement(attr::PlatformAttribute, artifact::AbstractPlatform, key::String)
    s = get(tags(artifact), key, nothing)
    return s === nothing ? attr.artifact_default : s
end
function host_value(attr::PlatformAttribute, host::AbstractPlatform, key::String)
    s = get(tags(host), key, nothing)
    return s === nothing ? attr.host_default : s
end

# The platforms are passed rather than their values, which are unions too large to split
function attribute_match(attr::PlatformAttribute, host::AbstractPlatform,
                         artifact::AbstractPlatform, key::String)
    req, have = requirement(attr, artifact, key), host_value(attr, host, key)
    req isa AnyValue && return CERTAIN_MATCH
    have isa UnknownValue && return POSSIBLE_MATCH
    r = parse_value(attr, req, artifact)
    h = parse_value(attr, have, host)
    # Values that do not parse only match an equal value
    (r === nothing || h === nothing) && return req == have ? CERTAIN_MATCH : NO_MATCH
    return satisfies_value(attr, r, h) ? CERTAIN_MATCH : NO_MATCH
end

# Rank of a requirement.  When the host value is known, a specific value beats `ANY`.  When
# it is unknown, a specific value relies on a guess, so it ranks below `ANY`.
const RANK_ANY = 1
function requirement_rank(req::Union{String,AnyValue}, have::Union{String,UnknownValue})
    req isa AnyValue && return RANK_ANY
    return have isa UnknownValue ? 0 : 2
end

function attribute_preference(attr::PlatformAttribute, host::AbstractPlatform,
                              pa::AbstractPlatform, pb::AbstractPlatform, key::String)
    ra, rb = requirement(attr, pa, key), requirement(attr, pb, key)
    have = host_value(attr, host, key)
    ka, kb = requirement_rank(ra, have), requirement_rank(rb, have)
    ka != kb && return ka > kb ? PREFER_FIRST : PREFER_SECOND
    ka == RANK_ANY && return PREFER_NEITHER
    ra, rb = ra::String, rb::String
    a = parse_value(attr, ra, pa)
    b = parse_value(attr, rb, pb)
    if a === nothing || b === nothing
        return ra == rb ? PREFER_NEITHER : INCOMPARABLE
    end
    return prefer_value(attr, a, b, have isa UnknownValue)
end

# A comparison strategy set on either platform (the pre-attribute extension mechanism).
# Strategies that implement exactly the semantics of a built-in attribute are ignored.
function legacy_strategy(host::AbstractPlatform, artifact::AbstractPlatform, key::String)
    function custom(p)
        p isa Platform || return nothing
        f = get(p.compare_strategies, key, nothing)
        f === nothing && return nothing
        f === compare_default && return nothing
        f === compare_julia_version && key == "julia_version" && return nothing
        f === compare_version_cap && key ∈ ("os_version", "cxxlib_version") && return nothing
        return f
    end
    hs, as = custom(host), custom(artifact)
    if hs !== nothing && as !== nothing && hs !== as
        throw(ArgumentError("Cannot compare Platform objects with two different non-default comparison strategies for the same key \"$(key)\""))
    end
    return hs === nothing ? as : hs
end

# The value of a missing tag for the built-in attribute of `key`, if it is the same
# concrete value on the host and the artifact side
function absent_value(key::String)
    attr = get(builtin_attributes, key, nothing)
    attr === nothing && return nothing
    a, h = attr.artifact_default, attr.host_default
    return (a isa String && h isa String && a == h) ? a : nothing
end

function attached_attribute(host::AbstractPlatform, key::String)
    host isa Platform || return nothing
    return get(host.attributes, key, nothing)
end
function key_attribute(host::AbstractPlatform, key::String)
    attr = attached_attribute(host, key)
    attr === nothing || return attr
    return get(() -> ExactAttribute(key), builtin_attributes, key)
end

# Calls a comparison strategy, which can be any function.  Overridden in trimmed images,
# which cannot call arbitrary functions.
call_compare_strategy(f, req::String, have::String, artifact_requested::Bool, host_requested::Bool) =
    @invokelatest(f(req, have, artifact_requested, host_requested))::Bool

function key_match(host::AbstractPlatform, artifact::AbstractPlatform, key::String)
    if attached_attribute(host, key) === nothing
        f = legacy_strategy(host, artifact, key)
        if f !== nothing
            # A missing tag on either side is a wildcard, as with `platforms_match`
            req = get(tags(artifact), key, nothing)
            have = get(tags(host), key, nothing)
            req === nothing && return CERTAIN_MATCH
            have === nothing && return POSSIBLE_MATCH
            artifact_requested = artifact isa Platform && get(artifact.compare_strategies, key, nothing) === f
            host_requested = host isa Platform && get(host.compare_strategies, key, nothing) === f
            ok = call_compare_strategy(f, req, have, artifact_requested, host_requested)
            return ok ? CERTAIN_MATCH : NO_MATCH
        end
    end
    return with_format(key_attribute(host, key)) do attr
        attribute_match(attr, host, artifact, key)
    end
end

function key_preference(host::AbstractPlatform, a::AbstractPlatform, b::AbstractPlatform, key::String)
    if attached_attribute(host, key) === nothing &&
            (legacy_strategy(host, a, key) !== nothing || legacy_strategy(host, b, key) !== nothing)
        # Comparison strategies carry no preference, beyond a specific value beating none
        ha, hb = haskey(tags(a), key), haskey(tags(b), key)
        return ha == hb ? PREFER_NEITHER : ha ? PREFER_FIRST : PREFER_SECOND
    end
    return with_format(key_attribute(host, key)) do attr
        attribute_preference(attr, host, a, b, key)
    end
end

function matching_keys(host::AbstractPlatform, artifacts)
    ks = Set{String}(keys(tags(host)))
    for p in artifacts
        union!(ks, keys(tags(p)))
    end
    host isa Platform && union!(ks, keys(host.attributes))
    prio(k) = something(findfirst(==(k), attribute_priority), length(attribute_priority) + 1)
    return sort!(collect(ks); by = k -> (prio(k), k))
end

function match_quality(host::AbstractPlatform, artifact::AbstractPlatform, ks=matching_keys(host, (artifact,)))
    q = CERTAIN_MATCH
    for key in ks
        q = min(q, key_match(host, artifact, key))
        q == NO_MATCH && break
    end
    return q
end

"""
    satisfies(host::AbstractPlatform, artifact::AbstractPlatform)

Return `true` if a binary built for the platform `artifact` can be used on `host`.  Unlike
[`platforms_match`](@ref), this is not symmetric: every tag is interpreted according to
its [`PlatformAttribute`](@ref), as a fact about the host on one side and as a requirement
of the artifact on the other.  A match that relies on host values that are unknown counts
as satisfied.
"""
satisfies(host::AbstractPlatform, artifact::AbstractPlatform) =
    match_quality(host, artifact) != NO_MATCH

# Whether `a` is at least as good as `b` on every key and strictly better on one
function dominates(host, a, b, ks)
    better = false
    for key in ks
        c = key_preference(host, a, b, key)
        (c == PREFER_SECOND || c == INCOMPARABLE) && return false
        c == PREFER_FIRST && (better = true)
    end
    return better
end

# Compare `a` and `b` key by key, in priority order
function lexicographic_preference(host, a, b, ks)
    for key in ks
        c = key_preference(host, a, b, key)
        (c == PREFER_FIRST || c == PREFER_SECOND) && return c
    end
    return PREFER_NEITHER
end

# The ordering that `select_platform` used before platform attributes; it now only
# resolves ambiguous selections.
function legacy_selection_order!(ps::Vector, platform::AbstractPlatform)
    function match_loss(a, b)
        a_tags = Set(keys(tags(a)))
        b_tags = Set(keys(tags(b)))
        return length(union(a_tags, b_tags)) - length(intersect(a_tags, b_tags))
    end
    sort!(ps, lt = (a, b) -> begin
        loss_a = match_loss(a, platform)
        loss_b = match_loss(b, platform)
        if loss_a != loss_b
            return loss_a < loss_b
        end
        return triplet(a) > triplet(b)
    end)
    return ps
end

# The best artifact platform among `ps` for `host`, or `nothing` if none matches
function select_platform_key(ps::Vector, host::AbstractPlatform)
    isempty(ps) && return nothing
    ks = matching_keys(host, ps)
    qualities = Int8[match_quality(host, p, ks) for p in ps]
    q = maximum(qualities)
    q == NO_MATCH && return nothing
    # Prefer matches that do not rely on unknown host values
    cands = ps[qualities .== q]
    length(cands) == 1 && return only(cands)

    # Keep the candidates that no other candidate beats on every key
    maximal = filter(a -> !any(b -> b !== a && dominates(host, b, a, ks), cands), cands)
    length(maximal) == 1 && return only(maximal)

    # Break remaining ties by key priority
    best = filter(a -> !any(b -> b !== a && lexicographic_preference(host, b, a, ks) == PREFER_FIRST, maximal), maximal)
    length(best) == 1 && return only(best)

    # The selection is ambiguous; fall back to the legacy ordering so that the result
    # stays deterministic.
    return first(legacy_selection_order!(isempty(best) ? maximal : best, host))
end

"""
    platforms_match(a::AbstractPlatform, b::AbstractPlatform)

Return `true` if `a` and `b` are matching platforms, where matching is determined by
comparing all keys contained within the platform objects, and if both objects contain
entries for that key, they must match.  Comparison, by default, is performed using
the `==` operator, however this can be overridden on a key-by-key basis by adding
"comparison strategies" through `set_compare_strategy!(platform, key, func)`.

Note that as the comparison strategy is set on the `Platform` object, and not globally,
a custom comparison strategy is first looked for within the `a` object, then if none
is found, it is looked for in the `b` object.  Finally, if none is found in either, the
default of `==(ak, bk)` is used.  We throw an error if custom comparison strategies are
used on both `a` and `b` and they are not the same custom comparison.

The reserved tags `os_version` and `libstdcxx_version` use this mechanism to provide
bounded version constraints, where an artifact can specify that it was built using APIs
only available in macOS `v"10.11"` and later, or an artifact can state that it requires
a libstdc++ that is at least `v"3.4.22"`, etc...

Keys present in only one of `a` or `b` are normally ignored.  The exception is a tag such
as `sanitize`, where a missing tag has a definite meaning: a sanitized platform (e.g.
`x86_64-linux-gnu-sanitize+memory`) never matches a platform without a `sanitize` tag,
since instrumented and uninstrumented binaries cannot be mixed.

To check whether an artifact can be used on a host, prefer [`satisfies`](@ref), which
interprets each tag according to its [`PlatformAttribute`](@ref).
"""
function platforms_match(a::AbstractPlatform, b::AbstractPlatform)
    for k in union(keys(tags(a)::Dict{String,String}), keys(tags(b)::Dict{String,String}))
        ak = get(tags(a), k, nothing)
        bk = get(tags(b), k, nothing)

        # A tag missing on one side is a wildcard, unless its built-in attribute gives a
        # missing tag the same concrete meaning on both sides (e.g. `sanitize`)
        if ak === nothing || bk === nothing
            absent = absent_value(k)
            absent === nothing && continue
            something(ak, absent) == something(bk, absent) || return false
            continue
        end

        a_comp = get_compare_strategy(a, k)
        b_comp = get_compare_strategy(b, k)

        # Throw an error if `a` and `b` have both set non-default comparison strategies for `k`
        # and they're not the same strategy.
        if a_comp !== compare_default && b_comp !== compare_default && a_comp !== b_comp
            throw(ArgumentError("Cannot compare Platform objects with two different non-default comparison strategies for the same key \"$(k)\""))
        end

        # Select the custom comparator, if we have one.
        comparator = a_comp
        if b_comp !== compare_default
            comparator = b_comp
        end

        # Call the comparator, passing in which objects requested this comparison (one, the other, or both)
        # For some comparators this doesn't matter, but for non-symmetrical comparisons, it does.
        if !(@invokelatest(comparator(ak, bk, a_comp === comparator, b_comp === comparator))::Bool)
            return false
        end
    end
    return true
end

function platforms_match(a::String, b::AbstractPlatform)
    return platforms_match(parse(Platform, a), b)
end
function platforms_match(a::AbstractPlatform, b::String)
    return platforms_match(a, parse(Platform, b))
end
platforms_match(a::String, b::String) = platforms_match(parse(Platform, a), parse(Platform, b))

# Adapters for AbstractString backedge avoidance
platforms_match(a::AbstractString, b::AbstractPlatform) = platforms_match(string(a)::String, b)
platforms_match(a::AbstractPlatform, b::AbstractString) = platforms_match(a, string(b)::String)
platforms_match(a::AbstractString, b::AbstractString) = platforms_match(string(a)::String, string(b)::String)


"""
    select_platform(download_info::Dict, platform::AbstractPlatform = HostPlatform())

Given a `download_info` dictionary mapping artifact platforms to some value, choose the
value whose key best matches the host `platform`, returning `nothing` if no artifact
platform [`satisfies`](@ref) the host.

Each tag is interpreted according to its [`PlatformAttribute`](@ref).  Among the matching
artifacts, those that do not rely on unknown host values are preferred.  An artifact is
then preferred over another if it is at least as good on every tag and better on one:
a specific value beats an artifact that works with any value, a newer version beats an
older one, a more specific microarchitecture beats a more generic one, and so on.
Remaining ties are broken tag by tag, in a fixed priority order.
"""
function select_platform(download_info::Dict, platform::AbstractPlatform = HostPlatform())
    best = select_platform_key(collect(keys(download_info)), platform)
    best === nothing && return nothing
    return download_info[best]
end

# precompiles to reduce latency (see https://github.com/JuliaLang/julia/pull/43990#issuecomment-1025692379)
Dict{Platform,String}()[HostPlatform()] = ""
Platform("x86_64", "linux", Dict{String,Any}(); validate_strict=true)
Platform("x86_64", "linux", Dict{String,String}(); validate_strict=false)  # called this way from Artifacts.unpack_platform

end # module
