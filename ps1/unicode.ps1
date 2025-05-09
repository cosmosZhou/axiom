$json = "json/abbreviations.json"
if (-not (Test-Path $json)) {
    Invoke-WebRequest -Uri "https://raw.githubusercontent.com/leanprover/vscode-lean4/master/lean4-unicode-input/src/abbreviations.json" -OutFile $json
}

# Read content as UTF-8, process, and filter
$content = Get-Content $json -Encoding utf8 | 
    ForEach-Object { $_ -replace '\$CURSOR', '' } |
    Where-Object { $_ -notmatch '"Longleftarrow|"Longleftrightarrow|"subseteqq|"supseteqq' }

# Save with UTF-8 without BOM using .NET method
$utf8NoBom = New-Object System.Text.UTF8Encoding $false
[System.IO.File]::WriteAllLines($json, $content, $utf8NoBom)