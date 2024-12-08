<?php
[, $password] = $set['eq'];
$sql = "set password = '$password'";

if ($password) {
    $rowcount = get_rows($sql);
    //error_log('$sql = '.$sql);
    redirect(auth_url($vendor, $server, $user));
}
else {
    if ($password == null)
        $set['eq'][1] = '';
    $dual = true;
}
?>