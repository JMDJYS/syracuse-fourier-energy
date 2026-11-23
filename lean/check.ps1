$ErrorActionPreference = 'Stop'
$tooling = Join-Path $PSScriptRoot '.tooling'
$lake = Join-Path $tooling 'lean-4.24.0-windows\bin\lake.exe'
$mathlib = Join-Path $tooling 'mathlib4-4.24.0'
$source1 = Join-Path $PSScriptRoot 'SyracuseEnergy.lean'
$source2 = Join-Path $PSScriptRoot 'PaperAudit.lean'
Push-Location -LiteralPath $mathlib
try {
    & $lake --packages=local-packages.json env lean -DwarningAsError=true $source1
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    & $lake --packages=local-packages.json env lean -DwarningAsError=true $source2
    exit $LASTEXITCODE
} finally {
    Pop-Location
}
