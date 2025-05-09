js=unpkg.com/vue@3.5.13/dist/vue.global.prod.js
dir=static/${js%/*}
mkdir -p $dir
cd $dir
wget https://$js