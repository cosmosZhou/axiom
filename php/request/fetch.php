<?php
require_once '../std.php';
$module = $_POST['module'];
$leanFile = str_replace('.', '/', $module) . ".lean";
chdir("../../");
$code = file_get_contents($leanFile);
echo std\encode(['code' => $code]);
?>

