<?php
require_once '../../utility.php';
require_once '../../mysql.php';
require_once '../../init.php';

use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;
$user = get_project_name();

$package = $dict['package'];
$section = $dict['section'];

error_log("package = $package");
error_log("section = $section");

$module = "$package.$section";
$path = module_to_path($module);

error_log("path = $path");

std\deleteDirectory($path);
$path = dirname($path);
error_log("dirname(path)= " . $path);
$files = iterator_to_array(std\read_files($path, "py"));
error_log("files = " . std\encode($files));

delete_from_lemma($user, '$module\b', true);

echo std\encode("deleted!");
