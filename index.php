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
            case "symbol":
                require_once 'php/symbol.php';
                exit();
            case "module":
                $module = $_GET['module'];
                break;
            case "axiom":
                $sympy = $_GET['axiom'];
                require_once 'php/sympy.php';
                exit();
            case "sympy":
                $sympy = $_GET['sympy'];
                require_once 'php/sympy.php';
                exit();
            case "callee":
                require_once 'php/hierarchy.php';
                exit();
            case "caller":
                require_once 'php/hierarchy.php';
                exit();
            case "new":
                require_once 'php/new.php';
                exit();
            case "state":
            case "keyword":
            case "latex":
                require_once 'php/search.php';
                exit();
        }
        break;
    case 2:
        $module = $_GET['module'];
        break;
    default:
        break;
}

function piece_together(&$input)
{
    $code = implode("\n", $input);
    $input = null;
    return $code;
}

function is_latex_print($latex, &$res)
{
    while (preg_match('/^(Eq\.\w+|\((Eq\.\w+|\*Eq\[-\d+:\]) *(, *Eq\.\w+)+ *\)|Eq\[-(\d+:|1)\]|\*Eq\[-\d+:\]|\*\w+|\w+)/u', $latex, $match)){
        $res[] = $match[0];
        $latex = std\slice($latex, strlen($match[0]));
        if (preg_match('/^ *= */', $latex, $matchEqual))
            return true;
        
        if (!preg_match('/^ *, */', $latex, $matchComma))
            return false;
        
        $latex = std\slice($latex, strlen($matchComma[0]));
    }
    
    return false;
}

$module = str_replace('/', '.', $module);
$title = str_replace('.', '/', $module);

$path_info = substr(__FILE__, 0, - 9) . "Axiom/" . $title;

$indexOfYield = - 1;
if (! str_ends_with($path_info, '/')) {

    $lean = $path_info . ".lean";
    if (file_exists($lean)) {
        $indexOfYield = 0;
        $logs = [];
        $ret = 1;

        if (array_key_exists('prove', $_POST)) {
            $applyCodes = array_key_exists('apply', $_POST) ? $_POST['apply'] : null;

            $proveCodes = $_POST['prove'];

            $proveCodes = insert_section($proveCodes);
            if (is_array($proveCodes))
                modify_codes($lean, $proveCodes, $applyCodes);
            else {
                error_log("create new lean file = $lean");

                $base_py = dirname($lean) . ".lean";
                if (file_exists($base_py)) {
                    $base_init = dirname($lean) . "/__init__.lean";
                    error_log("change $base_py into $base_init");
                    std\createDirectory(dirname($lean));

                    rename($base_py, $base_init);
                }

                $imports = [];
                if (file_exists($lean)) {
                    if (! str_ends_with($lean, "/__init__.lean"))
                        die("$lean already exists!");
                    else {
                        $file = new std\Text($lean);
                        if ($file->search('from util import \S')) {
                            die("$lean already exists!");
                        }
                        $imports = $file->preg_match('from \. import');
                    }
                }

                $file = new std\Text($lean);
                $code = "from util import *\n\n\n";

                $code .= $applyCodes . "\n";
                foreach (explode("\n", $proveCodes) as $line) {
                    $code .= "    $line\n";
                }

                $code .= "\n\nif __name__ == '__main__':\n";
                $code .= "    run()\n";

                $timestamp = date('Y-m-d', time());
                $code .= "# created on $timestamp\n";

                if (count($imports)) {
                    $code .= "\n\n";
                    $code .= implode("\n", $imports);
                }

                $file->write($code);

                insert_into_init(lean_to_module($lean));
            }

            [$logs, $data] = run($lean);
        }
        else
            $data = null;

        $lengths = [];

        $counterOfLengths = 0;

        $inputs = [];
        $input = [];

        $numOfRequisites = preg_match('/([\w.]+)\.to\./', $module, $m)? count(explode(".", $m[1])) - 1 : 0;

        $contents = [];
        $code = compile(file_get_contents($lean));

        $code = $code->render2vue();
    }
}

require_once $indexOfYield < 0 ? 'php/package.php' : 'php/theorem.php';
?>

