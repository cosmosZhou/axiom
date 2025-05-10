<?php
require_once '../std.php';
require_once '../lean/compile.php';
$module = $_POST['module'];

$leanFile = dirname(dirname(dirname(__FILE__))) . "/Lemma/" . str_replace('.', '/', $module) . ".lean";

$code = compile(file_get_contents($leanFile))->echo2vue($leanFile);
$code['module'] = $module;
echo json_encode($code);
?>

