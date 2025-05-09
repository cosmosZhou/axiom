url=unpkg.com/clipboard@2.0.11/dist/clipboard.min.js
dir=static/${url%/*}
mkdir -p $dir
cd $dir
wget https://$url
