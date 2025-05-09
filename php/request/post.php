<?php
require_once '../std.php';
if ($_POST)
    echo std\form_post($_POST['url'], $_POST['data'], false);
else {
    $input = file_get_contents('php://input');
    $input = std\decode($input);
    if ($header = $input['header']?? null)
        $header = array_map(fn($args) => "$args[0]: $args[1]", std\entries($header));

    if (function_exists('curl_init'))
        echo std\json_post($input['url'], $input['data'], $header, $input['id']?? null);
    else
        echo std\json_post_native($input['url'], $input['data'], $header, $input['id']?? null);
}
?>

