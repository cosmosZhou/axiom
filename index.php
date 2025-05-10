<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="static/css/style.css">
<?php
// ^ *error_log
require_once 'php/utility.php';
require_once 'php/mysql.php';
require_once 'php/lean/compile.php';


$key = array_keys($_GET);
switch (count($key)) {
    case 0:
        $key = array_keys($_POST);
        switch (count($key)) {
            case 0:
                require_once 'php/summary.php';
                exit();
            default:
                if (array_key_exists('module', $_POST)) {
                    $module = $_POST['module'];
                    break;
                } else {
                    require_once 'php/search.php';
                    exit();
                }
        }
        break;
    case 1:
        [$key] = $key;
        switch ($key) {
            case 'module':
                $module = $_GET['module'];
                break;
            case 'axiom':
                $sympy = $_GET['axiom'];
                require_once 'php/sympy.php';
                exit();
            case 'sympy':
                $sympy = $_GET['sympy'];
                require_once 'php/sympy.php';
                exit();
            case 'callee':
                require_once 'php/hierarchy.php';
                exit();
            case 'caller':
                require_once 'php/hierarchy.php';
                exit();
            case 'new':
                require_once 'php/new.php';
                exit();
            case 'type':
            case 'q':
            case 'latex':
                require_once 'php/search.php';
                exit();
        }
    case 2:
        $module = $_GET['module']?? null;
        if ($module)
            break;
    default:
        if ($_GET['q']?? null) {
            require_once 'php/search.php';
            exit();
        }
        if ($_GET['mathlib']?? null) {
            require_once 'php/mathlib.php';
            exit();
        }        
        break;
}

if (str_ends_with($module, '.lean')) {
    $module = lean_to_module($module);
    $user = get_project_name();
    header("location:?module=$module");
}

$module = str_replace('/', '.', $module);
$title = str_replace('.', '/', $module);

$path_info = substr(__FILE__, 0, -9) . "Lemma/" . $title;

$leanFile = null;
if (! str_ends_with($path_info, '/')) {
    $leanFile = $path_info . ".lean";
    if (!file_exists($leanFile)) {
        if ($_POST);
        elseif (file_exists($dirname = dirname($leanFile) . '.lean')) {
            $lastDotPosition = strrpos($module, '.');
            $module = substr($module, 0, $lastDotPosition) . '#' . substr($module, $lastDotPosition + 1);
            header("location:?module=$module");
        }
        else
            $leanFile = null;
    }
}

$php = $leanFile ? 'lemma' : 'package';
require_once  "php/$php.php";
?>