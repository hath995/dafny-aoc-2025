param ([Parameter(Mandatory)][int] $problem, [Parameter(Mandatory)][int] $part, [bool] $test)
if ($test) {
    $testSwitch = "-t"
} else {
    $testSwitch = ""
}
$i = 0
foreach ($cmd in Get-Command Dafny.exe) {
    $i = $i+1
}
if ($i -ne 0) {
    Dafny.exe run --no-verify --allow-warnings --unicode-char:true --target:cs "aoc-runner.dfy" --standard-libraries -- $problem $part $testSwitch
}else{
    Write-Output "Dafny.exe is not in terminal path."
}
