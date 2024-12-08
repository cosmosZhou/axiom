source common.sh

full_theorem=$(normalize $1)
echo full_theorem = $full_theorem

dst=Axiom/${full_theorem//.//}.lean
echo dst = $dst

if [ -f $dst ]; then
    echo "error: $dst already exists"
    exit
fi

install /dev/null -D $dst

echo -e "import Axiom.Basic\n" >> $dst

# Extract the all tokens before the last token
namespace=${full_theorem%.*}
echo "namespace = $namespace"
echo -e "namespace $namespace\n" >> $dst

# Extract the last token
theorem=${full_theorem##*.}
echo "theorem = $theorem"

theorem_string=$(echo $namespace | cut -d'.' -f2-)
echo "theorem_string = $theorem_string"
given=$(echo $theorem_string | sed 's/\.to.*//')
given=(${given//./ })
echo "given = ${given[@]}"
num_given=${#given[@]}

if [ "$num_given" -eq 0 ]; then
    comma=" :"
else
    comma=""
fi

echo "theorem $theorem$comma" >> $dst

digits=(₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉)
function subscript_digits {
    local str=$1
    for i in {0..9}; do
        str=${str//$i/${digits[$i]}}
    done
    echo $str
}

function CamelCase {
    echo $1 | awk '{
        while(match($0, /([A-Z][a-z_]*)/)) {
            print substr($0, RSTART, RLENGTH);
            $0 = substr($0, RSTART + RLENGTH);
        }
    }'
}

function match_case {
    case $1 in 
        Eq) echo "a = b" ;;
        Ne) echo "a ≠ b" ;;
        Gt) echo "a > b" ;;
        Lt) echo "a < b" ;;
        Ge) echo "a ≥ b" ;;
        Le) echo "a ≤ b" ;;
        In) echo "e ∈ s" ;;
        NotIn) echo "e ∉ s" ;;
        And) echo "p ∧ q" ;;
        Or) echo "p ∨ q" ;;
        Imply) echo "p → q" ;;
        Iff) echo "p ↔ q" ;;
        Not) echo "¬p" ;;
        All) echo "∀ x : α, p x" ;;
        Any) echo "∃ x : α, p x" ;;
        *) echo $1 ;;
    esac
}

function sample_proposition {
    list=$(CamelCase $1)
    list=($list)
    first=${list[0]}
    case "$first" in
        *_) 
        first=${first%_}
        echo $(match_case $first);;
        *) 
        echo $(match_case $first);;
    esac
}

if [ $num_given -gt 0 ]; then
    echo "-- given" >> $dst
    for i in $(seq 0 $((num_given - 1))); do
        if [ $num_given -eq 1 ]; then
            subscript_i=''
        else
            subscript_i=$(subscript_digits $i)
        fi
        
        sample_eq_i=$(sample_proposition ${given[$i]})

        if [ $i -eq $((num_given - 1)) ]; then
            comma=" :"
        else
            comma=""
        fi
        echo "  (h$subscript_i : $sample_eq_i)$comma" >> $dst
    done
fi

echo "-- imply" >> $dst
imply=$(echo $full_theorem | sed 's/.*to\.//')
imply=(${imply//./ })
echo "imply = ${imply[@]}"
sample_eq=$(sample_proposition ${imply[0]})
echo "  $sample_eq := by" >> $dst
echo "-- proof" >> $dst
echo -e "  sorry\n\n" >> $dst

echo "end $namespace" >> $dst

echo "-- created on $(date +%Y-%m-%d)" >> $dst
