<?php
include_once dirname(__file__).'/../std.php';

//is_array($table) && count($table) > 1
function parse_joined_table($table=null) {
    if (isset($table['join'])) {
        [$table, $table_joined] = $table['join'];

        if (is_string($table)) {
            if (is_array($table_joined)) {
                $entries = std\entries($table_joined);
                if (count($entries) == 1) {
                    [[$datable, $table]] = $entries;
                    if ($datable == 'as')
                        return [$datable, $table];
                    if (is_string($table))
                        return [$datable, $table];
                }
            }
            return ['corpus', $table];
        }

        if (array_key_exists('as', $table)) {
            [$table] = $table['as'];
            return get_db_table(["from" => $table]);
        }

        return get_db_table($table);
    }
    return [null, null];
}
function get_db_table($kwargs=null, $sql=null)
{
    $table = $kwargs['from']?? $kwargs['into']?? $kwargs['update'];
    if (is_array($table)) {
        if (count($table) > 1){
            if ($sql)
                return [null, null];
            return parse_joined_table($table);
        }

        [[$database, $table]] = std\entries($table);
        switch ($database) {
            case 'join':
            case 'cross_join':
            case 'inner_join':
            case 'left_join':
            case 'right_join':
            case 'full_join':
                if ($sql)
                    return [null, [$database => $table]];
                $table = $table[0];
                if (is_array($table))
                    return std\entries($table)[0];
                else
                    return [null, $table];
            case 'as':
                $table = $table[0];
                return $table;
        }

        if (preg_match('/\W/', $table))
            $table = "`$table`";
    }
    else 
        $database = 'corpus';

    if ($table == null) {
        if ($union = $kwargs['union']?? $kwargs['union_all']) {
            $db_table = array_map(fn(&$sql) => get_db_table($sql), $union);
            $db_table = std\zipped(...$db_table);
            return [...$db_table, true];
        }
        $table = 'reward';
    }

    return [$database, $table];
}

?>
