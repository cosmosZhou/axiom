<?php
require_once '../../mysql.php';

global $user;
[[$port]] = iterator_to_array(mysql\select("select port from login where user = '$user'"));

echo $port;
?>