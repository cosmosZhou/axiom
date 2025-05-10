<?php
require_once '../std.php';
echo std\encode(std\listdir(dirname(dirname(dirname(__FILE__))) . "/Lemma/"));
