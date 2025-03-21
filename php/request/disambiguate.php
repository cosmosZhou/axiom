<?php
require_once '../std.php';
require_once '../lean/compile.php';
$module = $_POST['module'];
$root = dirname(dirname(dirname(__FILE__))) . "/Axiom/";
$module = "/" . str_replace('.', '/', $module);
foreach ($_POST['section'] as $section) {
    $file = $root . $section . $module;
    if (file_exists($file) || file_exists($file . ".lean"))
        die($section);
}
