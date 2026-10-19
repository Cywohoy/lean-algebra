Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$projectRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$testRoot = Join-Path $PSScriptRoot ('exercise reset test-' + [guid]::NewGuid().ToString('N'))
$testTemplates = Join-Path $testRoot 'ExerciseTemplates'
$testWorking = Join-Path $testRoot 'Exercises'
$testBackups = Join-Path $testRoot 'exercise-backups'
$testResetScript = Join-Path $testRoot 'reset-exercises.ps1'
$testResetBatch = Join-Path $testRoot 'reset-exercises.bat'
$utf8 = New-Object System.Text.UTF8Encoding($false)

function Assert-True([bool]$Condition, [string]$Message) {
    if (-not $Condition) { throw $Message }
}
function Get-Hash([string]$Path) {
    (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash
}
function Get-LastBackup {
    @(Get-ChildItem -LiteralPath $testBackups -Directory | Sort-Object Name)[-1].FullName
}
function Write-Solutions([string[]]$Names) {
    foreach ($name in $Names) {
        [System.IO.File]::WriteAllText((Join-Path $testWorking $name),
            ('saved solution for ' + $name + ' ' + [guid]::NewGuid().ToString('N')), $utf8)
    }
}
function Invoke-Batch([string]$SectionName) {
    $startInfo = New-Object System.Diagnostics.ProcessStartInfo
    $startInfo.FileName = 'cmd.exe'
    $startInfo.Arguments = '/d /c ""' + $testResetBatch + '" ' + $SectionName + '"'
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardInput = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    $process = [System.Diagnostics.Process]::Start($startInfo)
    $process.StandardInput.WriteLine()
    $process.StandardInput.Close()
    if (-not $process.WaitForExit(15000)) {
        $process.Kill()
        throw 'Batch reset timed out.'
    }
    $batchOutput = $process.StandardOutput.ReadToEnd()
    $batchError = $process.StandardError.ReadToEnd()
    Assert-True ($process.ExitCode -eq 0) ('Batch reset failed: ' + $batchOutput + $batchError)
    $process.Dispose()
}

try {
    New-Item -ItemType Directory -Path $testTemplates, $testWorking -Force | Out-Null
    foreach ($template in Get-ChildItem -LiteralPath (Join-Path $projectRoot 'ExerciseTemplates') -Filter '*.lean' -File) {
        Copy-Item -LiteralPath $template.FullName -Destination (Join-Path $testTemplates $template.Name)
    }
    Copy-Item -LiteralPath (Join-Path $projectRoot 'reset-exercises.ps1') -Destination $testResetScript
    Copy-Item -LiteralPath (Join-Path $projectRoot 'reset-exercises.bat') -Destination $testResetBatch
    $names = @((Get-ChildItem -LiteralPath $testTemplates -Filter '*.lean' -File).Name)
    Write-Solutions $names

    $before = @{}
    foreach ($name in $names) { $before[$name] = Get-Hash (Join-Path $testWorking $name) }
    & $testResetScript -Section Cardinality | Out-Null
    $backup = Get-LastBackup
    Assert-True ((Get-Hash (Join-Path $testWorking 'Cardinality.lean')) -eq
        (Get-Hash (Join-Path $testTemplates 'Cardinality.lean'))) 'Selected section was not reset.'
    Assert-True ((Get-Hash (Join-Path $backup 'Cardinality.lean')) -eq $before['Cardinality.lean']) 'Original solution was not backed up.'
    Assert-True (@(Get-ChildItem -LiteralPath $backup -File).Count -eq 1) 'Selective reset backed up unrelated files.'
    foreach ($name in $names) {
        if ($name -ne 'Cardinality.lean') {
            Assert-True ((Get-Hash (Join-Path $testWorking $name)) -eq $before[$name]) 'An unrelated worksheet changed.'
        }
    }
    Write-Output 'PASS: selective reset and backup'

    Write-Solutions $names
    & $testResetScript | Out-Null
    $backup = Get-LastBackup
    Assert-True (@(Get-ChildItem -LiteralPath $backup -File).Count -eq $names.Count) 'Full reset did not back up all worksheets.'
    foreach ($name in $names) {
        Assert-True ((Get-Hash (Join-Path $testWorking $name)) -eq
            (Get-Hash (Join-Path $testTemplates $name))) 'Full reset did not restore all templates.'
    }
    Assert-True (@(Get-ChildItem -LiteralPath $testBackups -Directory).Count -eq 2) 'Backup folders were reused.'
    Write-Output 'PASS: full reset and separate backup folders'

    Write-Solutions @('Proofs.lean', 'Sets.lean', 'Functions.lean')
    $functionHash = Get-Hash (Join-Path $testWorking 'Functions.lean')
    & $testResetScript -Section Proofs, Sets | Out-Null
    foreach ($name in @('Proofs.lean', 'Sets.lean')) {
        Assert-True ((Get-Hash (Join-Path $testWorking $name)) -eq
            (Get-Hash (Join-Path $testTemplates $name))) 'Multiple-section reset failed.'
    }
    Assert-True ((Get-Hash (Join-Path $testWorking 'Functions.lean')) -eq $functionHash) 'Multiple-section reset changed an unrelated file.'
    Write-Output 'PASS: multiple-section reset'

    $backupCount = @(Get-ChildItem -LiteralPath $testBackups -Directory).Count
    $rejected = $false
    try { & $testResetScript -Section Unknown | Out-Null }
    catch { $rejected = $true }
    Assert-True $rejected 'Unknown section was accepted.'
    Assert-True (@(Get-ChildItem -LiteralPath $testBackups -Directory).Count -eq $backupCount) 'Invalid input created a backup.'
    Assert-True ((Get-Hash (Join-Path $testWorking 'Functions.lean')) -eq $functionHash) 'Invalid input changed a worksheet.'
    Write-Output 'PASS: invalid section leaves worksheets unchanged'

    $backupCount = @(Get-ChildItem -LiteralPath $testBackups -Directory).Count
    $rejected = $false
    try { & $testResetScript -Section All, Proofs | Out-Null }
    catch { $rejected = $true }
    Assert-True $rejected 'Mixed All and section names were accepted.'
    Assert-True (@(Get-ChildItem -LiteralPath $testBackups -Directory).Count -eq $backupCount) 'Invalid mixed input created a backup.'
    Write-Output 'PASS: mixed All and section names are rejected'

    & $testResetScript -Section Functions.lean, Functions | Out-Null
    $backup = Get-LastBackup
    Assert-True (@(Get-ChildItem -LiteralPath $backup -File).Count -eq 1) 'Duplicate section names were not deduplicated.'
    Write-Output 'PASS: filename arguments and duplicate selections'

    $missingPath = Join-Path $testWorking 'Sets.lean'
    Remove-Item -LiteralPath $missingPath
    & $testResetScript -Section Sets | Out-Null
    Assert-True ((Get-Hash $missingPath) -eq
        (Get-Hash (Join-Path $testTemplates 'Sets.lean'))) 'Missing worksheet was not recreated.'
    Write-Output 'PASS: missing worksheet is recreated'

    Write-Solutions @('Proofs.lean', 'Functions.lean')
    $functionHash = Get-Hash (Join-Path $testWorking 'Functions.lean')
    Invoke-Batch 'Proofs'
    Assert-True ((Get-Hash (Join-Path $testWorking 'Proofs.lean')) -eq
        (Get-Hash (Join-Path $testTemplates 'Proofs.lean'))) 'Batch section argument was ignored.'
    Assert-True ((Get-Hash (Join-Path $testWorking 'Functions.lean')) -eq $functionHash) 'Batch selective reset changed another file.'
    Invoke-Batch ''
    foreach ($name in $names) {
        Assert-True ((Get-Hash (Join-Path $testWorking $name)) -eq
            (Get-Hash (Join-Path $testTemplates $name))) 'Batch default did not reset all worksheets.'
    }
    Write-Output 'PASS: both batch entry points'

    Write-Solutions @('Proofs.lean', 'Sets.lean')
    $proofsHash = Get-Hash (Join-Path $testWorking 'Proofs.lean')
    $blockedPath = Join-Path $testWorking 'Sets.lean'
    Remove-Item -LiteralPath $blockedPath
    New-Item -ItemType Directory -Path $blockedPath | Out-Null
    $rejected = $false
    try { & $testResetScript -Section Proofs, Sets | Out-Null }
    catch { $rejected = $true }
    Assert-True $rejected 'A directory was accepted as a worksheet.'
    Assert-True ((Get-Hash (Join-Path $testWorking 'Proofs.lean')) -eq $proofsHash) 'A worksheet was reset before all backups completed.'
    Write-Output 'PASS: incomplete backup prevents all overwrites'
}
finally {
    if (Test-Path -LiteralPath $testRoot) {
        $resolvedTestRoot = (Resolve-Path -LiteralPath $testRoot).Path
        $allowedTestPrefix = [System.IO.Path]::GetFullPath($PSScriptRoot).TrimEnd('\') + '\'
        if (-not $resolvedTestRoot.StartsWith($allowedTestPrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
            throw 'Test cleanup path is outside the temporary directory.'
        }
        Remove-Item -LiteralPath $resolvedTestRoot -Recurse -Force
    }
}
