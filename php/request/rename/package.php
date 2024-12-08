<?php
require_once '../../utility.php';
require_once '../../mysql.php';
require_once '../../init.php';
use std\Graph, std\Text, std\Set;

$user = get_user();

$dict = empty($_POST) ? $_GET : $_POST;

if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'package::',
        'old::',
        'new::'
    ]);
    $dict['package'] = str_replace('/', '.', $dict['package']);
}

$package = $dict['package'];
$old = $dict['old'];
$new = $dict['new'];

error_log("package = $package");
error_log("old = $old");
error_log("new = $new");

$folder = axiom_directory() . str_replace('.', '/', $package) . '/';

// $folder = str_replace("\\", '/', axiom_directory()) . str_replace('.', '/', $package) . '/';

error_log("folder = $folder");

function rename_folder()
{
    global $folder;
    global $package;
    global $old, $new;

    $oldPyPath = $folder . $old . "/__init__.lean";

    $oldPy = new Text($oldPyPath);
    if ($oldPy->search('^@apply\b')) {
        $lines = $oldPy->retain('from \. import \w+');
        $oldPyPath = $folder . $old . ".lean";
        $oldPy = new Text($oldPyPath);
        $oldPy->writelines($lines);

        if (! rename($folder . $old, $folder . $new)) {
            die("failed in renaming: $folder$old => $folder$new");
        }

        insert_into_init($package, $new);
    } else {
        std\renameDirectory($folder . $old, $folder . $new);

        if (file_exists($folder . $new . ".lean")) {
            $newPy = new Text($folder . $new . ".lean");
            $lines = $newPy->readlines();

            unlink($folder . $new . ".lean");

            $__init__ = new Text($folder . $new . "/__init__.lean");
            $__init__->insert(0, $lines);

            insert_into_init($package, $new);
            delete_from_init($package, $old);
        } else {
            replace_into_init($package, $old, $new);
        }
    }
}

if (strpos($new, '.') !== false) {
    error_log("found . in new!");
    $subPackages = explode('.', $new);
    $new = end($subPackages);

    $subFolder = $folder . implode("/", array_slice($subPackages, 0, - 1)) . '/';
    error_log("subFolder = $subFolder");
    std\createDirectory($subFolder);

    if (file_exists($folder . $old . ".lean")) {
        if (! file_exists($subFolder . $new . ".lean")) {

            $prefix = '';
            foreach ($subPackages as $module) {
                insert_into_init("$package$prefix", $module);
                $prefix .= ".$module";
            }

            if (rename($folder . $old . ".lean", $subFolder . $new . ".lean")) {

                $old = "$package.$old";

                $subPackage = implode(".", array_slice($subPackages, 0, - 1));
                $new = "$package.$subPackage.$new";

                delete_from_suggest($user, $old);
                insert_into_suggest($user, $new);
                update_axiom($user, $old, $new);
                update_hierarchy($user, $old, $new);
            } else {
                die("renaming failed");
            }
        } else {
            die("$subPackage unimplemented!");
        }
    } else {
        $__init__ = $folder . $old . "/__init__.lean";
        if (file_exists($__init__)) {

            $import = [];
            $statement = [];
            $text = new std\Text($__init__);

            foreach ($text as $line) {
                if (preg_match('/from \. import +/', $line, $m))
                    $import[] = $line;
                else
                    $statement[] = $line;
            }

            if ($subPackage == $old) {
                $import[] = "from . import $new";
            }

            $text->writelines($import);

            $py = new std\Text($subFolder . $new . ".lean");
            $py->writelines($statement);

            if ($subPackage == $old) {
                $old = "$package.$old";
                $new = "$package.$subPackage.$new";

                insert_into_suggest($user, $new);
                update_axiom($user, $old, $new);
                update_hierarchy($user, $old, $new);
            } else {
                die("$subPackage unimplemented!");
            }
        }
    }
} else {
    $oldAxiom = "$package.$old";
    
    if ($new == null) {
        $newAxiom = $package;
    } else
        $newAxiom = "$package.$new";
        
    update_hierarchy($user, $oldAxiom, $newAxiom, true);
        
    if (is_dir($folder . $new)) {
        $newPyPath = $folder . $new . "/__init__.lean";
        if (file_exists($newPyPath)) {
            $newPy = new Text($newPyPath);
            if ($newPy->search('^@apply\b')) {
                die($newPyPath . " already exists");
            }

            $oldPyPath = $folder . $old . ".lean";
            $oldPy = new Text($oldPyPath);

            $newPy->insert(0, $oldPy->readlines());

            unlink($oldPyPath);
            delete_from_init($package, $old);
        } else {
            std\deleteDirectory($folder . $new);
            rename_folder();
        }
    } else {
        rename_folder();
    }

    update_suggest($user, $package, $old, $new, true);
    update_axiom($user, $oldAxiom, $newAxiom, true);
}

echo std\encode("renamed!");
?>