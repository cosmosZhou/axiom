json=json/abbreviations.json
if [ ! -f $json ]; then
    wget -O $json https://raw.githubusercontent.com/leanprover/vscode-lean4/master/lean4-unicode-input/src/abbreviations.json
fi

sed -i -E 's/\$CURSOR//g' $json
sed -i '/"Longleftarrow/d' $json
sed -i '/"Longleftrightarrow/d' $json
sed -i '/"subseteqq/d' $json
sed -i '/"supseteqq/d' $json
