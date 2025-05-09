<?php
require_once '../std.php';
require_once '../lean/compile.php';

try {
    $code = compile($_POST['lean'] . "\n");
    if ($code->args[0] instanceof LCaret) 
        array_shift($code->args);
    $code = rtrim("$code");
    echo std\encode(['lean' => $code]);
} catch (Exception $e) {
    echo std\encode(['error' => $e->getMessage()]);
}
