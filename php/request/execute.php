<?php
require_once '../utility.php';
require_once '../init.php';
$resultType = $_POST['resultType']?? MYSQLI_NUM;
$result = mysql\execute($_POST['sql'], $resultType);
if (is_array($result))
    $result = std\encode($result);
echo $result;
?>