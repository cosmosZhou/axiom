<?php
require_once '../../mysql.php';

global $user;
$max = - 1;
foreach (mysql\select("select port from login") as [$port]) {
    if ($port > $max) {
        $max = $port;
    }
}

$port = max($max + 1, 5000);

mysql\execute("update login set port = $port where user = '$user'");

// dirname(dirname(__file__)) . "/run.py";

// $cmd = "\"D:\\Users\\a\\AppData\\Local\\Programs\\Python\\Python39\\pythonw.exe\" run.py port=$port";
// error_log($cmd);
// exec($cmd);
// tasklist | findstr pythonw
// taskkill /F /im pythonw.exe

echo $port;
?>