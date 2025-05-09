url=unpkg.com/lz-string@1.5.0/libs/lz-string.js
dir=static/${url%/*}
mkdir -p $dir
cd $dir
wget https://$url
