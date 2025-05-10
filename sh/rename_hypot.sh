# Define subscript characters using Unicode escapes
subscripts=(
    $'\u2080'  # ₀
    $'\u2081'  # ₁
    $'\u2082'  # ₂
    $'\u2083'  # ₃
    $'\u2084'  # ₄
    $'\u2085'  # ₅
    $'\u2086'  # ₆
    $'\u2087'  # ₇
    $'\u2088'  # ₈
    $'\u2089'  # ₉
)

function rename {
    curr=$1
    prev=$2
    # echo "Processing replacement from $curr to $prev"
    # Find files containing 'curr' but not 'prev' and process them
    grep -rlZ --include='*.lean' --exclude='*.echo.lean' -E "\\b$curr" Lemma \
    | xargs -0 grep -LZ -E "\\b$prev" \
    | while IFS= read -r -d $'\0' file; do
        echo "Processing file: $file, Renaming $curr to $prev in:"
        grep -nE "\\b$curr" "$file"
        sed -i -E "s/\\b$curr/$prev/g" "$file"
    done
}

# Iterate from h₁ to h₉
for i in {1..9}; do
    rename "h${subscripts[i]}" "h${subscripts[i-1]}"
done

# Now replace h₀ with h if h is not detected
rename "h${subscripts[0]}" "h"