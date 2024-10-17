# This file is a part of Julia. License is MIT: https://julialang.org/license

Downloads() = require(PkgId(
        UUID((0xf43a241f_c20a_4ad4, 0x852c_f6b1247861c6)),
        "Downloads",
    ))

"""
    download(url::AbstractString, [path::AbstractString = tempname()]) -> path

Download a file from the given url, saving it to the location `path`, or if not
specified, a temporary path. Returns the path of the downloaded file.

!!! note
    Since Julia 1.6, this function is deprecated and is just a thin wrapper
    around `Downloads.download`. In new code, you should use that function
    directly instead of calling this.
"""
download(url::AbstractString, path::AbstractString) = do_download(url, path)
download(url::AbstractString) = do_download(url, nothing)

function do_download(url::AbstractString, path::Union{AbstractString, Nothing})
    depwarn("Base.download is deprecated; use Downloads.download instead", :download)
    invokelatest(Downloads().download, url, path)
end

module DownloadsHooks

"""
`EASY_HOOK` is a modifable global hook to used as the default `easy_hook` on
new `Downloader` objects. This supplies a mechanism to set options for the
`Downloader` via `Curl.setopt`

It is expected to be function taking two arguments: an `Easy` struct and an
`info` NamedTuple with names `url`, `method` and `headers`.
"""
const EASY_HOOK = Ref{Union{Function, Nothing}}(nothing)

end # module
