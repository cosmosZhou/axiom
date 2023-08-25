<?php
require_once '../std.php';
if ($_POST) {
    echo std\form_post($_POST['url'], $_POST['data'], false);    
}
else {
    $data = file_get_contents('php://input');
    $data = std\decode($data);
    echo std\json_post($data['url'], $data['data']);    
}
?>

