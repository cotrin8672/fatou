param(
    [Parameter(Mandatory = $true)]
    [string]$Fatou
)

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $true
$fatouPath = (Resolve-Path -LiteralPath $Fatou).Path
$id = [Guid]::NewGuid().ToString('N').Substring(0, 12)
$root = Join-Path ([IO.Path]::GetTempPath()) "fatou-network-$id"
$fixtureHome = "$root-home"
$shareName = "fatou-$id"
$unc = "\\localhost\$shareName"
$drive = @('Z:', 'Y:', 'X:', 'W:') | Where-Object { -not (Get-PSDrive -Name $_[0] -ErrorAction SilentlyContinue) -and -not (Get-SmbMapping -LocalPath $_ -ErrorAction SilentlyContinue) } | Select-Object -First 1
if (-not $drive) { throw 'No test drive letter is free' }
$shared = $false
$mapped = $false
try {
    $source = Join-Path $root 'source folder'
    $null = New-Item -Path (Join-Path $source 'result_stdout') -ItemType Directory -Force
    Set-Content -LiteralPath (Join-Path $root 'Project.toml') -Encoding ascii -Value @'
[workspace]
projects = ["source folder"]
'@
    Set-Content -LiteralPath (Join-Path $source 'Project.toml') -Encoding ascii -Value @'
[deps]
MAT = "23992714-dd62-5051-b70f-ba57cb901cac"
Roots = "f2b01f46-fcfa-551c-844a-d8ac1e96c665"
Dagger = "d58978e5-989f-55fb-8d15-ea34adc7bf54"
FFTW = "7a1cc6ca-52ef-59f5-83cd-3a7055c09341"
'@
    # Minimal offline index fixtures at the actual registered-version slugs.
    # These are smoke-test source stubs: they are not runnable package installs.
    Set-Content -LiteralPath (Join-Path $root 'Manifest.toml') -Encoding ascii -Value @'
julia_version = "1.13.4"
manifest_format = "2.0"

[[deps.MAT]]
git-tree-sha1 = "4ca9560153a5cb28a567c029bbe27290d2f325d6"
uuid = "23992714-dd62-5051-b70f-ba57cb901cac"
version = "0.13.0"

[[deps.Roots]]
git-tree-sha1 = "2c8f6d5798bbb31b65d2ef65e660ab7fc00f7683"
uuid = "f2b01f46-fcfa-551c-844a-d8ac1e96c665"
version = "3.0.15"

[[deps.Dagger]]
path = "fixture-pkgs/Dagger"
uuid = "d58978e5-989f-55fb-8d15-ea34adc7bf54"
version = "0.22.7"

[[deps.FFTW]]
deps = ["AbstractFFTs"]
path = "fixture-pkgs/FFTW"
uuid = "7a1cc6ca-52ef-59f5-83cd-3a7055c09341"
version = "1.10.0"

[[deps.AbstractFFTs]]
path = "fixture-pkgs/AbstractFFTs"
uuid = "621f4979-c628-5d54-868e-fcf4e3e8185c"
version = "1.5.0"
'@
    $mat = Join-Path $fixtureHome '.julia\packages\MAT\0dW40\src'
    $roots = Join-Path $fixtureHome '.julia\packages\Roots\pl0ND\src'
    $null = New-Item -Path $mat,$roots -ItemType Directory -Force
    Set-Content -LiteralPath (Join-Path $mat 'MAT.jl') -Encoding ascii -Value @'
module MAT
export matread
matread(path) = path
end
'@
    Set-Content -LiteralPath (Join-Path $roots 'Roots.jl') -Encoding ascii -Value @'
module Roots
export find_zero
find_zero(f, initial) = initial
end
'@
    foreach ($package in @('Dagger', 'FFTW', 'AbstractFFTs')) {
        $null = New-Item -Path (Join-Path $root "fixture-pkgs/$package/src") -ItemType Directory -Force
    }
    Set-Content -LiteralPath (Join-Path $root 'fixture-pkgs/Dagger/src/Dagger.jl') -Encoding ascii -Value @'
module Dagger
export @spawn
macro spawn(work)
    esc(work)
end
end
'@
    Set-Content -LiteralPath (Join-Path $root 'fixture-pkgs/AbstractFFTs/src/AbstractFFTs.jl') -Encoding ascii -Value @'
module AbstractFFTs
export fft
fft(x) = x
end
'@
    Set-Content -LiteralPath (Join-Path $root 'fixture-pkgs/FFTW/src/FFTW.jl') -Encoding ascii -Value @'
module FFTW
using Reexport
@reexport using AbstractFFTs
end
'@
    Set-Content -LiteralPath (Join-Path $source 'entry.jl') -Value '# disk marker; test sends unsaved buffer contents' -Encoding ascii
    Set-Content -LiteralPath (Join-Path $source 'result_script.jl') -Value 'f() = 42' -Encoding ascii
    Set-Content -LiteralPath (Join-Path $source 'result_data.toml') -Value 'count = 42' -Encoding ascii
    Set-Content -LiteralPath (Join-Path $source 'result_stdout\child.txt') -Value 'nested fixture' -Encoding ascii

    Start-Service -Name LanmanServer
    $identity = [Security.Principal.WindowsIdentity]::GetCurrent().Name
    $null = New-SmbShare -Name $shareName -Path $root -FullAccess $identity
    $shared = $true
    if (-not (Test-Path -LiteralPath "$unc\source folder\entry.jl")) { throw "Local SMB is not readable at $unc" }
    $null = New-SmbMapping -LocalPath $drive -RemotePath $unc -Persistent $false
    $mapped = $true
    if (-not (Test-Path -LiteralPath "$drive\source folder\entry.jl")) { throw "SMB drive is not readable at $drive" }

    # Use the actual drive designator; PowerShell-only drives and SUBST do not exercise SMB.
    node (Join-Path $PSScriptRoot 'windows-network-smoke.mjs') $fatouPath $unc "$drive/" $fixtureHome
} finally {
    if ($mapped) { Remove-SmbMapping -LocalPath $drive -Force -ErrorAction Continue }
    if ($shared) { Remove-SmbShare -Name $shareName -Force -ErrorAction Continue }
    if (Test-Path -LiteralPath $root) { Remove-Item -LiteralPath $root -Recurse -Force -ErrorAction Continue }
    if (Test-Path -LiteralPath $fixtureHome) { Remove-Item -LiteralPath $fixtureHome -Recurse -Force -ErrorAction Continue }
}
