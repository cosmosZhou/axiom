source utility.sh
# lake env lean $leanFile
jsonFile=$(build_object $1)
cat $jsonFile
rm $jsonFile