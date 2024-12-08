<?php
require_once '../std.php';
if ($_POST) {
    echo std\form_post($_POST['url'], $_POST['data'], false);
}
else {
    $input = file_get_contents('php://input');
    $input = std\decode($input);
    if ($header = $input['header']) {
        $header = array_map(fn($args) => "$args[0]: $args[1]", std\entries($header));
    }

    // error_log('$url = '.$input['url']);
    // error_log('$data = '.std\encode($input['data']));
    // error_log('$id = '.$input['id']);
    echo std\json_post($input['url'], $input['data'], $header, $input['id']);
}
?>

