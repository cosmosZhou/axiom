<?php
require_once '../../utility.php';
require_once '../../mysql.php';
require_once '../../init.php';
use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;
$user = get_user();

$package = $dict['package'];
$section = $dict['section'];

error_log("package = $package");
error_log("section = $section");

$module = "$package.$section";
$path = module_to_path($module);

error_log("path = $path");

$initPath = "$path/__init__.py";

if (file_exists($initPath)){
    $init = new Text($initPath);
    if ($init->search('^@apply\b')) {
        
        foreach (scandir($path) as $file) {
            switch ($file) {
                case ".":
                case "..":
                    break;
                case "__init__.py":
                    break;
                default:
                    $file = "$path/$file";
                    if (is_dir($file)) {
                        std\deleteDirectory($file);
                    } else {
                        unlink($file);
                    }
            }
        }
        
        rename($initPath, "$path.py");
        
        delete_from_suggest($user, $module, true);
        delete_from_axiom($user, "$module\..+", true);
    } else {
        std\deleteDirectory($path);
        delete_from_init($package, $section);
        delete_from_suggest($user, $module);
        delete_from_axiom($user, '$module\b', true);
    }    
}
else{
    std\deleteDirectory($path);
    $path = dirname($path);
    error_log("dirname(path)= ".$path);
    $files = iterator_to_array(std\read_files($path, "py"));
    error_log("files = ".std\encode($files));
    if (count($files) == 1){
        [$__init__] = $files;
        if (str_ends_with($__init__, "/__init__.py") || str_ends_with($__init__, "\\__init__.py")){
            $substrPyInit = substr($__init__, 0, -12) . ".py";
            if (!rename($__init__, $substrPyInit)){
                error_log("failed in renaming $__init__ to $substrPyInit");
            }
            
            std\deleteDirectory($path);
        }
    }
    
    delete_from_init($package, $section);
    
    delete_from_suggest($user, $module);
    
    delete_from_axiom($user, '$module\b', true);    
}

echo std\encode("deleted!");
?>