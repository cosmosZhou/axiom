function normalize() {
    case "$1" in
        *.lean) 
            src=${1#*Axiom/}
            src=${src%.lean}
            src=(${src//// })
            # if the first element is "Axiom", remove it
            if [ ${src[0]} == "Axiom" ]; then
                src=("${src[@]:1}")
            fi
            # join the array with "."
            src=${src[*]}
            echo "${src// /.}"
            ;;
        Axiom.*)
            echo ${1#Axiom.}
            ;;
        *) 
            echo $1
            ;;
    
    esac
}

# Define the array_map function
array_map() {
    local func="$1"
    shift
    local array=("$@")
    local result=()

    for element in "${array[@]}"; do
        result+=("$("$func" "$element")")
    done

    echo "${result[@]}"
}

lake_build_lib() {
    echo "$1/.lake/build/lib"
}

# Define the transformation function
get_lean_path() {
    packages=$(ls -d .lake/packages/*)
    packages=$(array_map lake_build_lib $packages)
    packages=${packages// /:}
    echo $packages:.lake/build/lib
}

build_object() {
    theorem=$(normalize $1)
    baseFile=Axiom/${theorem//./\/}
    leanFile=${baseFile}.lean
    oleanFile=.lake/build/lib/${baseFile}.olean
    ileanFile=.lake/build/lib/${baseFile}.ilean
    jsonFile=.lake/build/lib/${baseFile}.json
    cFile=.lake/build/ir/${baseFile}.c
    LEAN_PATH=$(get_lean_path) lean -Dpp.unicode.fun=true -Dlinter.dupNamespace=false $leanFile -R . -o $oleanFile -i $ileanFile -c $cFile --json > $jsonFile
    echo $jsonFile    
}
