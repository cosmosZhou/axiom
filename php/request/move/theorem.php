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
} else {
    $old .= "/__init__.lean";
}

$new = $folder . str_replace(".", "/", $dest) . "/$basename";

error_log("old = $old");
error_log("new = $new");

if (file_exists($new . ".lean")) {
    $new .= "/__init__.lean";

    $newFile = new std\Text($new);
    if ($newFile->search('^@apply\b')) {
        die("$newFile already exists!");        
    }

    $newFile->rewind();
    $content = $newFile->read();

    rename($old, $new);

    $newFile = new std\Text($new);

    $newFile->append("\n$content");
} else {
    $new .= ".lean";
    rename($old, $new);
}

delete_from_init($oldPackage, $basename);

insert_into_init($dest, $basename);

$old = $oldPackage.".".$basename;
$new = $dest.".".$basename;

$user = get_user();
update_axiom($user, $old, $new);
delete_from_suggest($user, $old);
insert_into_suggest($user, $new);
update_hierarchy($user, $old, $new);

echo true;
?>