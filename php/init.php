<?php
include "include/driver.inc.php"; // must be included as last driver
include "include/mysql.inc.php"; // must be included as last driver
include "include/functions.inc.php"; // must be included as last driver

$connection = new Min_DB;

$host = ini_get("mysqli.default_host");
if (!$host) 
    $host = "127.0.0.1";
$user = ini_get("mysqli.default_user") ?? "user";
$password = ini_get("mysqli.default_pw")?? "user";
$database = 'axiom';
$port = ini_get("mysqli.default_port");
mysqli_report(MYSQLI_REPORT_OFF);

$connection->options(MYSQLI_OPT_LOCAL_INFILE, true);
$return = @$connection->real_connect($host, $user, $password, $database, $port);
?>
