<?php
require_once '../../utility.php';
require_once '../../mysql.php';
require_once '../../init.php';

use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;

$theorem = $dict['theorem'];
error_log("theorem = $theorem");

preg_match('/(.+)\.(\w+)$/', $theorem, $m);
$oldPackage = $m[1];
$dest = $dict['dest'];
error_log("dest = $dest");

$folder = axiom_directory();

error_log("folder = $folder");

$old = $folder . str_replace('.', '/', $theorem);

$basename = basename($old);

error_log("basename = $basename");

if (file_exists($old . ".lean")) {
    $old .= ".lean";
}

$new = $folder . str_replace(".", "/", $dest) . "/$basename";

error_log("old = $old");
error_log("new = $new");

$new .= ".lean";
rename($old, $new);

$old = $oldPackage . "." . $basename;
$new = $dest . "." . $basename;

$user = get_project_name();
update_axiom($user, $old, $new);

echo true;
