$COQ_PATH="coqc"
$PREFIX=" -R . IPC2 "

Function compile($name , $ignoredate) {
    $Tab = [char]9
    Write-Host("")
    $dateA = (Get-Item ("$($name).v")).LastWriteTime
    if (Test-Path "$($name).vo") {
        $dateB = (Get-Item ("$($name).vo")).LastWriteTime
    }
    else {
        $dateB = $dateA
    }
    if ($ignoredate) {
        Write-Host("compiling " + $name)
        cmd /c ($COQ_PATH + $PREFIX + $name)
        return $TRUE
    }
    elseif ($dateA -ge $dateB) {
      Write-Host("compiling " + $name)
      cmd /c ($COQ_PATH + $PREFIX + $name)
      return $TRUE
    } else {
      Write-Host($name + ".v $Tab modified before " + $name + ".vo")
      return $FALSE
    }
}

$ignoredate = $FALSE
$ignoredate = compile "UserTactics" $ignoredate
$ignoredate = compile "ListFacts" $ignoredate
$ignoredate = compile "MiscFacts" $ignoredate
$ignoredate = compile "Seq" $ignoredate
$ignoredate = compile "Label" $ignoredate
$ignoredate = compile "Formula" $ignoredate
$ignoredate = compile "FormulaFacts" $ignoredate
$ignoredate = compile "Term" $ignoredate
$ignoredate = compile "Diophantine" $ignoredate
$ignoredate = compile "Derivations" $ignoredate
$ignoredate = compile "Encoding" $ignoredate
$ignoredate = compile "Soundness" $ignoredate
$ignoredate = compile "Completeness" $ignoredate
$ignoredate = compile "MainResult" $ignoredate

Write-Host("")
Read-Host 'Press Enter to continue...' | Out-Null