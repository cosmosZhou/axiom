<?php
[, $password] = $set['eq'];
$sql = "set password = '$password'";

if ($password) {
    $rowcount = get_rows($sql);
    redirect(auth_url($vendor, $server));
}
else {
    if ($password == null)
        $set['eq'][1] = '';
    $dual = true;
}
?>