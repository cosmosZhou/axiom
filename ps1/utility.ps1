function normalize {
    param (
        [string]$inputString
    )

    switch -Wildcard ($inputString) {
        "*.lean" {
            $src = $inputString -replace "^.*?Lemma/", ""
            $src = $src -replace "\.lean$", ""
            $parts = $src -split "/"
            
            if ($parts[0] -eq "Lemma") {
                $parts = $parts[1..($parts.Length-1)]
            }
            
            return $parts -join "."
        }
        
        "Lemma.*" {
            return $inputString -replace "^Lemma\.", ""
        }
        
        default {
            return $inputString
        }
    }
}

function array_map {
    param (
        [scriptblock]$Func,
        [array]$Array
    )

    $Array | ForEach-Object { & $Func $_ }
}

function lake_build_lib {
    param ([string]$path)
    Join-Path $path ".lake/build/lib"
}

function get_lean_path {
    $packages = Get-ChildItem .lake/packages -Directory | Select-Object -ExpandProperty FullName
    $processed = array_map -Func { lake_build_lib $_ } -Array $packages
    ($processed -join ":") + ":.lake/build/lib"
}

function build_object {
    param (
        [string]$theoremInput
    )

    $theorem = normalize $theoremInput
    $baseFile = "Lemma/" + ($theorem -replace '\.', '/')
    $leanFile = "$baseFile.lean"
    $oleanFile = ".lake/build/lib/$baseFile.olean"
    $ileanFile = ".lake/build/lib/$baseFile.ilean"
    $jsonFile = ".lake/build/lib/$baseFile.json"
    $cFile = ".lake/build/ir/$baseFile.c"

    $env:LEAN_PATH = get_lean_path
    lean -Dpp.unicode.fun=true -Dlinter.dupNamespace=false "$leanFile" -R . -o "$oleanFile" -i "$ileanFile" -c "$cFile" --json | Out-File $jsonFile -Encoding utf8

    return $jsonFile
}

function batches {
    param(
        [Parameter(Mandatory=$true)]
        [array]$Data,
        [Parameter(Mandatory=$true)]
        [int]$BatchSize
    )

    $size = $Data.Count
    $divisor = [int](($size + $BatchSize - 1) / $BatchSize)
    $batches = @()
    if ($divisor -ne 0) {
        $quotient = [int]($size / $divisor)
        $sizes = @(for ($i = 0; $i -lt $divisor; $i++) { $quotient })

        $remainder = $size % $divisor
        for ($i = 0; $i -lt $remainder; $i++) {
            $sizes[$i] += 1
        }

        
        $start = 0
        foreach ($length in $sizes) {
            $stop = $start + $length
            $batches += ,@($Data[$start..($stop - 1)])
            $start = $stop
        }
    } else {
        $batches += ,@($Data)
    }
    return $batches;
}