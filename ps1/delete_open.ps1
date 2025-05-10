# List of package names to process
$packages = Get-ChildItem -Path "Lemma" -Directory | Select-Object -ExpandProperty Name

# Loop over each package
foreach ($package in $packages) {
    $escapedPackage = [regex]::Escape($package)
    $patternOpen = "open ([\w]+ )*$escapedPackage\b"
    $importPattern = "import Lemma\.$escapedPackage\."

    # Find files with open statement but without import
    $filesWithOpen = Get-ChildItem -Path Lemma -Recurse -Include '*.lean' -Exclude '*.echo.lean' | Where-Object {
        (Select-String -Path $_.FullName -Pattern $patternOpen -Quiet)
    }
    
    $filesToProcess = $filesWithOpen | Where-Object {
        -not (Select-String -Path $_.FullName -Pattern $importPattern -Quiet)
    }

    # Process each file
    foreach ($file in $filesToProcess) {
        Write-Host "Processing file: $($file.FullName)"
        Write-Host "The following lines will be modified (removing '$package' from 'open' statements):"
        
        # Show lines to be modified
        $lines = Get-Content $file.FullName
        $lines | ForEach-Object -Begin { $i = 1 } -Process {
            if ($_ -match $patternOpen) {
                "$i : $_"
            }
            $i++
        }

        # Modify file content
        $newContent = $lines | ForEach-Object {
            $line = $_
            if ($line -match '^open ') {
                # Remove package name
                $newLine = $line -replace "\b$escapedPackage\b", ''
                # Collapse spaces
                $newLine = $newLine -replace ' +', ' '
                # Trim trailing space
                $newLine = $newLine.TrimEnd()
                # Skip empty 'open' lines
                if ($newLine -eq 'open') { $null } else { $newLine }
            } else {
                $line
            }
        } | Where-Object { $_ -ne $null }

        # Write changes back to file
        $newContent | Set-Content -Path $file.FullName
    }
}