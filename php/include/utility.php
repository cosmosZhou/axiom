<?php
include_once dirname(__file__).'/../std.php';

function get_db_table($kwargs=null)
{
    if ($kwargs == null)
        $kwargs = $_GET;

    $value = $kwargs['from']?? $kwargs['into']?? $kwargs['update'];
    if (is_array($value)) {
        [$tuple] = std\entries($value);
        switch ($tuple[0]) {
            case 'join':
            case 'cross_join':
            case 'inner_join':
            case 'left_join':
            case 'right_join':
            case 'full_join':
                return $tuple[1][0];
        }
        return $tuple;
    }

    if ($value == null)
        $value = 'rlhf';

    return ['corpus', $value];
}

?>
