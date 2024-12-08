<?php
$sql = "show ".parse_expression($show);
error_log('$sql = '.$sql);
$data = get_rows($sql);
error_log('$data = '.std\encode($data));
$dual = true;
?>