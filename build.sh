source common.sh
# lake env lean $leanFile
jsonFile=$(build_theorem $1)
cat $jsonFile
rm $jsonFile