<?php
require_once '../utility.php';
require_once '../mysql.php';
require_once '../init.php';

$dict = empty($_POST) ? $_GET : $_POST;
$prefix = $dict['prefix'];
echo std\encode(hint($prefix));

?>