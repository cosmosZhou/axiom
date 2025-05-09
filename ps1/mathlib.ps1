# usage: powershell sh/mathlib.ps1

# Check if MYSQL_USER is set
if (-not $env:MYSQL_USER) {
    Write-Host "MYSQL_USER is not set. Please ensure it is set in your environment."
    exit 1
}

# Generate json/mathlib.jsonl if missing
if (-not (Test-Path "json/mathlib.jsonl")) {
    Write-Host "Building Mathlib..."
    Measure-Command { lake build Mathlib } | Out-Host
    Write-Host "Generating mathlib.jsonl..."
    Measure-Command { lake env lean sympy/printing/mathlib.lean | Out-File "json/mathlib.jsonl" -Encoding utf8 } | Out-Host
}

# Generate json/mathlib.tsv if missing
if (-not (Test-Path "json/mathlib.tsv")) {
    # Check if jq is available
    if (-not (Get-Command "jq" -ErrorAction SilentlyContinue)) {
        # Install jq if missing
        # Define paths and URLs
        $jqUrl = "https://github.com/jqlang/jq/releases/download/jq-1.7.1/jq-windows-amd64.exe"
        $mingwBin = Join-Path $env:MINGW_HOME "bin"
        # rename to jq.exe and put it at the directory %MINGW_HOME%/bin
        $jqPath = Join-Path $mingwBin "jq.exe"
        
        # Create MINGW bin directory if it doesn't exist
        if (-not (Test-Path $mingwBin)) {
            New-Item -Path $mingwBin -ItemType Directory -Force | Out-Null
        }
        
        # Download and install jq
        Write-Host "Installing jq to $mingwBin..."
        Invoke-WebRequest -Uri $jqUrl -OutFile $jqPath
    }
    jq -r '[.name, .type] | @tsv' json/mathlib.jsonl | Out-File "json/mathlib.tsv"
}

# Run MySQL import and log output
Get-Content "sql/insert/mathlib.sql" | mysql --local-infile=1 -u$env:MYSQL_USER -p$env:MYSQL_PASSWORD -P$env:MYSQL_PORT -D axiom *>&1 | Tee-Object -FilePath "test.log"

# Check if the error indicates missing table
$pattern = "ERROR \d+ \(\w+\) at line \d+: Table 'axiom\.mathlib' doesn't exist"
if (Select-String -Path "test.log" -Pattern $pattern -Quiet) {
    Write-Host "Table 'mathlib' does not exist. Creating it..."
    
    # Execute create SQL script
    Get-Content "sql/create/mathlib.sql" | mysql -u$env:MYSQL_USER -p$env:MYSQL_PASSWORD -P$env:MYSQL_PORT -D axiom
    
    if ($?) {
        Write-Host "Table 'mathlib' created successfully. Re-running script..."
        & $MyInvocation.MyCommand.Path @args
    } else {
        Write-Host "Failed to create table 'mathlib'."
        exit 1
    }
}