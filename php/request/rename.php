<?php
require_once '../utility.php';
require_once '../mysql.php';
require_once '../init.php';
use std\Graph, std\Text, std\Set;

$user = get_user();

$dict = empty($_POST) ? $_GET : $_POST;

if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'old::',
        'new::'
    ]);
    
    $dict['old'] = "Keras.Eq_Cup.to.Eq.Dot.Softmax.batch_gather";
    $dict['new'] = "Keras.Eq_Card.Subset_Cup.to.Eq.Dot.Softmax.batch_gather";
}

$old = $dict['old'];
$new = $dict['new'];

error_log("old = $old");
error_log("new = $new");

$oldPy = module_to_py($old);
$newPy = module_to_py($new);

if (! str_ends_with($newPy, "/__init__.lean")) {
    if (filesize($newPy)){
        die("$newPy already exists");
    }
    else{
        unlink($newPy);
    }
}

error_log("oldPy = $oldPy");

if (file_exists($newPy)) {
    error_log("newPy = $newPy");
    
    if (str_ends_with($oldPy, "/__init__.lean")) {
        $__init__ = new Text($oldPy);

        $newPyText = new Text($newPy);
        $newPyText->writelines($__init__->retain('^from \. import \w+'));
    } else {
        $newPy = new Text($newPy);
        $oldPyText = new Text($oldPy);
        $newPy->insert(0, $oldPyText->readlines());

        error_log("deleting $oldPy");
        if (!unlink($oldPy)){
            error_log("Error in deleting $oldPy");            
        }

        delete_from_init($old);
    }
    insert_into_init($new);
} else {
    $newPy = substr($newPy, 0, - strlen("/__init__.lean")) . ".lean";
    error_log("newPy = $newPy");
    
    std\createDirectory(dirname($newPy));

    if (str_ends_with($oldPy, "/__init__.lean")) {
        $__init__ = new Text($oldPy);
        
        $newPyText = new Text($newPy);
        $newPyText->writelines($__init__->retain('^from \. import \w+'));
        insert_into_init($new);
    } else {
        
        $substr = substr($new, 0, strrpos($new, '.'));        
        $substrPy = module_to_py($substr);
        if (! str_ends_with($substrPy, "/__init__.lean")) {
            $substrPyInit = substr($substrPy, 0, -3) . "/__init__.lean";
            if (dirname($substrPyInit).".lean" == $oldPy){
                $__init__ = new Text($substrPyInit);
                $newPackages = explode('.', $new);
                $newPackageLast = end($newPackages);
                $__init__->write("from . import $newPackageLast");
            }
            else{
                if (! rename($substrPy, $substrPyInit)) {
                    die("failed in renameing $substrPy to $substrPyInit");
                }
            }
        }
        
        error_log("renaming from $oldPy to $newPy");
        if (! rename($oldPy, $newPy)) {
            die("failed in renameing $oldPy to $newPy");
        }

        delete_from_init($old);
        insert_into_init($new);
    }
}

delete_from_suggest($user, $old);
insert_into_suggest($user, $new);

update_axiom($user, $old, $new);
update_hierarchy($user, $old, $new);

echo std\encode("renamed!");
?>