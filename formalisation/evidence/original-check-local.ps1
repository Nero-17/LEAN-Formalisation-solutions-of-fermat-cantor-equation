param([string]$Module = 'LambdaCantor.lean')
$ErrorActionPreference = 'Stop'
if ($Module.StartsWith('LambdaCantor/')) {
  $urgentPath = Join-Path $PSScriptRoot ('.root-before-' + [System.IO.Path]::GetFileNameWithoutExtension($Module) + '.txt')
  if (Test-Path -LiteralPath $urgentPath) {
    $urgentModules = Get-Content -LiteralPath $urgentPath
    Remove-Item -LiteralPath $urgentPath
    foreach ($urgentModule in $urgentModules) {
      if ($urgentModule.Trim()) {
        & (Join-Path $PSScriptRoot 'check-local.ps1') $urgentModule
        Write-Output "URGENT_COMPILE_RESULT $urgentModule $LASTEXITCODE"
      }
    }
  }
}
$packageRoot = 'C:\Users\lzysh\Documents\Codex\lean32\packages'
 $sourcePath = Join-Path $PSScriptRoot $Module
 if (Test-Path -LiteralPath $sourcePath) {
   $sourceText = Get-Content -LiteralPath $sourcePath -Raw
   foreach ($importMatch in [regex]::Matches($sourceText, '(?m)^\s*(?:public\s+)?import\s+(LambdaCantor\.[\w.]+)')) {
     $dependencyPath = Join-Path $PSScriptRoot (($importMatch.Groups[1].Value -replace '\.', '/') + '.olean')
     if (-not (Test-Path -LiteralPath $dependencyPath)) {
       Write-Output "DEPENDENCY_NOT_BUILT $($importMatch.Groups[1].Value) REQUIRED_BY $Module"
       exit 1
     }
   }
 }
$env:LEAN_PATH = (($PSScriptRoot) + ';' + ((Get-ChildItem $packageRoot -Directory | ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' }) -join ';'))
Push-Location $PSScriptRoot
$compileLock = $null
$lockDeadline = [DateTime]::UtcNow.AddMinutes(120)
try {
  while ($null -eq $compileLock) {
    $priorityPath = Join-Path $PSScriptRoot '.compile-priority.json'
    if (Test-Path -LiteralPath $priorityPath) {
      $priority = Get-Content -LiteralPath $priorityPath -Raw | ConvertFrom-Json
      if (([DateTime]::UtcNow -lt ([DateTime]$priority.expiresUtc).ToUniversalTime()) -and ($Module -notin $priority.modules)) {
        Start-Sleep -Milliseconds 500
        continue
      }
    }
    try { $compileLock = [System.IO.File]::Open((Join-Path $PSScriptRoot '.compile.lock'), [System.IO.FileMode]::OpenOrCreate, [System.IO.FileAccess]::ReadWrite, [System.IO.FileShare]::None) }
    catch [System.IO.IOException] {
      if ([DateTime]::UtcNow -gt $lockDeadline) { throw 'Timed out waiting for shared Lean compilation slot.' }
      Start-Sleep -Milliseconds (Get-Random -Minimum 150 -Maximum 450)
    }
  }
  $logDirectory = Join-Path $PSScriptRoot 'build-logs'
  New-Item -ItemType Directory -Force $logDirectory | Out-Null
  $logFile = Join-Path $logDirectory (($Module -replace '[/\\]', '_') + '.log')
  $sourceHash = (Get-FileHash -LiteralPath $Module -Algorithm SHA256).Hash
  "UTC=$([DateTime]::UtcNow.ToString('o')) MODULE=$Module SHA256=$sourceHash" | Set-Content -LiteralPath $logFile
  $compileTimer = [System.Diagnostics.Stopwatch]::StartNew()
  & 'C:\Users\lzysh\.elan\toolchains\leanprover--lean4---v4.32.1\bin\lean.exe' -j 1 -o ($Module -replace '\.lean$', '.olean') $Module 2>&1 | Tee-Object -FilePath $logFile -Append
  $leanExitCode = $LASTEXITCODE
  $compileTimer.Stop()
  "ELAPSED_SECONDS=$($compileTimer.Elapsed.TotalSeconds) END_UTC=$([DateTime]::UtcNow.ToString('o'))" | Add-Content -LiteralPath $logFile
  "EXIT=$leanExitCode" | Add-Content -LiteralPath $logFile
  exit $leanExitCode
} finally {
  if ($null -ne $compileLock) { $compileLock.Dispose() }
  Start-Sleep -Milliseconds 1500
  Pop-Location
}
