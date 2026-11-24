param([string[]] $Modules = @('Cycle108Computed'), [int] $Threads = 2, [switch] $Rebuild)

$ErrorActionPreference = 'Stop'
$mathRoot = Join-Path (Split-Path $PSScriptRoot -Parent) 'syracuse-energy-lean\.tooling'
$lean = Join-Path $mathRoot 'lean-4.24.0-windows\bin\lean.exe'
$mathlib = Join-Path $mathRoot 'mathlib4-4.24.0'
$output = Join-Path $PSScriptRoot '.build'
[IO.Directory]::CreateDirectory($output) | Out-Null
$paths = @($output, (Join-Path $mathlib '.lake\build\lib\lean'))
$packages = Join-Path $mathlib '.lake\packages'
$paths += @(Get-ChildItem -Directory -LiteralPath $packages |
    ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' })
$env:LEAN_PATH = $paths -join ';'
$visited = [Collections.Generic.HashSet[string]]::new()

function Build-Module([string] $module) {
    if ($module -notmatch '^[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z0-9_]+)*$') {
        throw "Invalid module name $module"
    }
    if (!$visited.Add($module)) { return }
    $relative = $module.Replace('.', '\')
    $source = Join-Path $PSScriptRoot "$relative.lean"
    $artifact = Join-Path $output "$relative.olean"
    $sourceInfo = Get-Item -LiteralPath $source
    $latest = $sourceInfo.LastWriteTimeUtc
    $imports = [regex]::Matches([IO.File]::ReadAllText($source),
        '(?m)^import\s+([A-Za-z][A-Za-z0-9_.]*)')
    foreach ($dependency in $imports) {
        $name = $dependency.Groups[1].Value
        $dep = $name.Replace('.', '\')
        if (!(Test-Path -LiteralPath (Join-Path $PSScriptRoot "$dep.lean"))) { continue }
        Build-Module $name
        $depTime = (Get-Item -LiteralPath (Join-Path $output "$dep.olean")).LastWriteTimeUtc
        if ($depTime -gt $latest) { $latest = $depTime }
    }
    if (!$Rebuild -and (Test-Path -LiteralPath $artifact) -and
        (Get-Item -LiteralPath $artifact).LastWriteTimeUtc -ge $latest) { return }
    [IO.Directory]::CreateDirectory((Split-Path $artifact -Parent)) | Out-Null
    Write-Output "Checking $module"
    & $lean -j $Threads -o $artifact $source
    if ($LASTEXITCODE -ne 0) { throw "Lean rejected $module (exit $LASTEXITCODE)" }
}

Push-Location -LiteralPath $PSScriptRoot
try {
    foreach ($module in $Modules) { Build-Module $module }
} finally {
    Pop-Location
}
