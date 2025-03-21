<?php
require_once '../std.php';
$name = $_POST['name'];

$leanFile = "test.$name.lean";
chdir("../../");
if (!file_exists($leanFile)) {
    error_log("create new lean file = $leanFile");
    std\createNewFile($leanFile);
}
// create a block to write the code
{
    $file = new std\Text($leanFile);
    $codeStr = <<< EOT
import Mathlib
import sympy.printing.json
#eval do
  println! ← Name.toJson `$name
EOT;

    $file->writelines([$codeStr]);
}

$cmd = "~/.elan/bin/lake env lean \"$leanFile\"";
error_log("executing cmd = $cmd");
exec($cmd, $output_array);
echo implode("\n", $output_array);

unlink($leanFile);
?>

