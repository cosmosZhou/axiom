<?php
include "include/driver.inc.php"; // must be included as last driver
include "include/mysql.inc.php"; // must be included as last driver
include "include/functions.inc.php"; // must be included as last driver

$connection = new Min_DB;

$host = "127.0.0.1";
$user = "prod";
$password = "prod";
$database = 'axiom';
$port = ini_get("mysqli.default_port");
mysqli_report(MYSQLI_REPORT_OFF);

$connection->options(MYSQLI_OPT_LOCAL_INFILE, true);
$return = @$connection->real_connect(
    ($host != "" ? $host : ini_get("mysqli.default_host")),
    ($host . $user != "" ? $user : ini_get("mysqli.default_user")),
    ($host . $user . $password != "" ? $password : ini_get("mysqli.default_pw")),
    $database,
    $port);
?>
