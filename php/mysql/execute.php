<?php
require_once '../mysql.php';
$sql = $_POST['sql'];

$is_array = is_array($sql);
$is_select = $is_array? std\array_all(fn (&$statement) => preg_match("/^(desc|select|show)\W/", $statement), $sql):preg_match("/^(desc|select|show)\W/", $sql);
if (!$is_select && !mysql\is_admin()) {
    if (!array_key_exists('master', $_POST)) {
        die('0');
    }
}

//error_log("executing sql = ".std\encode($sql));

if ($is_array) {
    if (array_key_exists('dictionary', $_POST)){
        $result = mysql\multi_query($sql, MYSQLI_ASSOC);
    }
    else{
        $result = mysql\multi_query($sql);
    }
}
else {
    if (array_key_exists('dictionary', $_POST)){
        $result = mysql\execute($sql, MYSQLI_ASSOC);
    }
    else{
        $result = mysql\execute($sql);
    }
}

//error_log("result = ".std\encode($result));
echo std\encode($result);
?>