<?php
require_once '../utility.php';

$arr = [];

$topk = $_GET['top'];

$folder = axiom_directory();

$topKHeap = new std\TopKHeap($topk);
foreach (read_all_axioms($folder) as [$pyFile, $php]) {
    $py = file($pyFile);
    $count = count($py);
    
    $module = py_to_module($php);
    if (!$count){
        error_log($pyFile." is empty!");
        try {
            unlink($pyFile);
        } catch (Exception $e) {
            error_log($e->getMessage());
        }
        
        continue;
    }
    
    $updatedTime = $py[$count - 1];
    if (preg_match("/(\d\d\d\d)-(\d\d)-(\d\d)/", $updatedTime, $m)){
        $element = [(int)$m[1], (int)$m[2], (int)$m[3], $module];        
        $topKHeap->push($element);
    }
}

$arr = $topKHeap->topk();

$res = [];
foreach ($arr as [,,, $module]){
    $res[] = $module;
}
echo std\encode($res);
?>