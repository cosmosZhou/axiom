<?php
require_once '../utility.php';
require_once '../mysql.php';
require_once '../init.php';

$user = get_project_name();

function rename_lemma($old, $new)
{
    $cmd = "cd ../../sh && bash rename.sh $old $new";
    exec($cmd, $output_array, $ret);
    
    error_log(implode("\n", $output_array));
    
    if ($ret)
        error_log("Error in renaming $old to $new");
}

$dict = empty($_POST) ? $_GET : $_POST;

$package = $dict['package']?? null;
$old = $dict['old'];
$new = $dict['new'];

error_log("old = $old");
error_log("new = $new");
if ($package !== null) {
    $oldLemma = "$package$old";
    $newLemma = "$package$new";
    update_lemma($user, $oldLemma, $newLemma, true, function($old, $new) use ($user) {
        rename_lemma($old, $new);
    });

    update_axiom($user, $oldLemma, $newLemma, true);
    $folder = axiom_directory() . str_replace('.', '/', $package) . '/';
    std\deleteDirectory($folder . $old);
} else {

    $newFile = module_to_lean($new);

    if (filesize($newFile))
        die("$newFile already exists");

    unlink($newFile);

    rename_lemma($old, $new);

    update_axiom($user, $old, $new);
}

echo std\encode("renamed!");
