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
$folder = axiom_directory() . str_replace('.', '/', $package);

if (!str_ends_with($folder, "/")){
    $folder .= '/';
}

error_log("folder = $folder");

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

//             $import[] = "from . import $subPackages[1]";
            $text->writelines($import);

            $py = new std\Text($subFolder . $new . ".lean");
            $py->writelines($statement);

            $old = "$package.$old";
            $new = "$package." . implode(".", $subPackages);

            insert_into_suggest($user, $new);
            update_axiom($user, $old, $new);
            update_hierarchy($user, $old, $new);
            
            insert_into_init($new);
        }
    }
} else {

    if (is_dir($folder . $new)) {
        $newPyPath = $folder . $new . "/__init__.lean";
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

        if (file_exists($folder . $old . ".lean")) {
            if (! rename($folder . $old . ".lean", $folder . $new . ".lean")) {
                die("failed in renaming: $folder.$old.lean => $folder.$new.lean");
            }
            replace_into_init($package, $old, $new);
        } else {
            $oldPath = $folder . $old . "/__init__.lean";

            assert(file_exists($oldPath));
            $oldText = new Text($oldPath);
            $lines = $oldText->retain('from \. import \w+');
            $newText = new Text($folder . $new . ".lean");
            $newText->writelines($lines);

            insert_into_init($package, $new);
        }
    }

    update_suggest($user, $package, $old, $new);
    $old = "$package.$old";

    if ($new == null) {
        $new = $package;
    } else
        $new = "$package.$new";

    update_axiom($user, $old, $new);
    update_hierarchy($user, $old, $new);
}

echo std\encode("renamed!");
?>