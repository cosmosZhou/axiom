<?php
require_once '../../utility.php';
require_once '../../mysql.php';
require_once '../../init.php';

$dict = empty($_POST) ? $_GET : $_POST;
$user = get_project_name();

$package = $dict['package'];
$lemma = $dict['lemma'];

$package = str_replace('/', '.', $package);
if (str_ends_with($package, '.'))
    $package = substr($package, 0, -1);
error_log("package = $package");
error_log("lemma = $lemma");

$module = "$package.$lemma";
$file = module_to_lean($module);
error_log("file = $file");

unlink($file);

delete_from_lemma($user, $module);
echo std\encode("deleted!");
