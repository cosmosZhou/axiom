<?php
echo json_encode(str_replace("\\", "\\\\", trim(sys_get_temp_dir())));
?>

