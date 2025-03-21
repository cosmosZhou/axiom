clipboard_js=unpkg.com/clipboard@2.0.11/dist/clipboard.min.js
clipboard_dir=static/${clipboard_js%/*}
mkdir -p $clipboard_dir
cd $clipboard_dir
wget https://$clipboard_js
