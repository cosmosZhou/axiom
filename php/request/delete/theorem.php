<?php
require_once '../../utility.php';
require_once '../../mysql.php';
require_once '../../init.php';
use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;
$user = get_user();
if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'package::',
        'theorem::'
    ]);
}

$package = $dict['package'];
$theorem = $dict['theorem'];

error_log("package = $package");
error_log("theorem = $theorem");

$module = "$package.$theorem";
$py = module_to_py($module);
error_log("py = $py");

if (str_ends_with($py, "/__init__.py")) {
    $init = new Text($py);
    $lines = $init->preg_match('^from . import \w+');
    $init->writelines($lines);

    delete_from_suggest($user, $module, true);
} else {
    unlink($py);
    delete_from_init($package, $theorem);

    delete_from_suggest($user, $module);
}

delete_from_axiom($user, $module);
echo std\encode("deleted!");
?>