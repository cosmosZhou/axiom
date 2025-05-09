url=unpkg.com/vue3-sfc-loader@0.9.5/dist/vue3-sfc-loader.js
dir=static/${url%/*}
mkdir -p $dir
cd $dir
wget https://$url
