<!DOCTYPE html>
<html lang=en>
<meta charset="UTF-8">
<link rel="shortcut icon" href="static/favicon.ico" type="image/x-icon" />
<title><?php echo $vue?></title>
<body></body>
</html>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js" <?php echo $nonce? nonce() : ''?>></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js" <?php echo $nonce? nonce() : ''?>></script>

<script src="static/unpkg.com/clipboard@2.0.11/dist/clipboard.min.js" <?php echo $nonce? nonce() : ''?>></script>
<script src="static/unpkg.com/file-saver@2.0.5/dist/FileSaver.min.js" <?php echo $nonce? nonce() : ''?>></script>

<script src="static/unpkg.com/vue@3.2.47/dist/vue.global.prod.js" <?php echo $nonce? nonce() : ''?>></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js" <?php echo $nonce? nonce() : ''?>></script>
<script src="static/js/std.js" <?php echo $nonce? nonce() : ''?>></script>

<script type=module <?php echo $nonce? nonce() : ''?>>
createApp('<?php echo $vue?>', <?php echo $props? std\encode($props): "{}"?>);
</script>
