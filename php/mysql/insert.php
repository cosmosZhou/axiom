<?php
$Field2Type = mysql\field_to_type($kwargs['into']);

$keys = array_keys($Field2Type);

// error_log("\$Field2Type = ".std\encode($Field2Type));

$values = [];

foreach ($keys as $key) {
    if (! array_key_exists($key, $_POST))
        continue;
    $values[$key] = $_POST[$key];
    if ($Field2Type[$key] == 'text')
        $values[$key] = str_replace("\r\n", "\n", $values[$key]);
}

if (! in_array('training', $keys))
    $values['training'] = $_POST['training'];

$seq_param = [];
$seq_param_with_inputs = [];
$data = [];

$keys = array_filter($keys, fn($key) => !str_starts_with($key, '__') || !str_ends_with($key, '__'));
$keys_rest = [...$keys];

$primary_key = $Field2Type['__primary_key__'];
std\removeFrom($primary_key, $keys_rest);
// error_log("values = ".std\encode($values));

function transform_specials(&$data) {
    if (is_string($data)) {
        $data = str_replace("\r\n", "\n", $data);
        $data = str_replace("\\r\\n", "\n", $data);
        $data = str_replace("\r", "\n", $data);
        return $data;
    }
    else if (std\is_list($data))
        return array_map(fn($arg) => transform_specials($arg), $data);
    else if (is_array($data)){
        $result = [];
        foreach($data as $key => &$value) {
            $result[$key] = transform_specials($value);
        }
        return $result;
    }
    else
        return $data;
}

if ($values['training']) {
    foreach ($values['training'] as $i => $training) {
        $training = (int)$training;
        if ($training >= 0)
            continue;

        $training = ~ $training;

        $datum = [];
        foreach ($keys as $key) {
            $datum[$key] = $values[$key][$i];

            if (mysql\is_varchar($Field2Type[$key]))
                $datum[$key] = str_replace("\r\n", "\n", $datum[$key]);
            else if (is_array($datum[$key])) {
                $datum[$key] = transform_specials($datum[$key]);
                $datum[$key] = std\encode($datum[$key]);
            }
            else if (mysql\is_json($Field2Type[$key])){
                $datum[$key] = std\decode($datum[$key]);
                $datum[$key] = transform_specials($datum[$key]);
                $datum[$key] = std\encode($datum[$key]);
            }
        }

        if ($training & 64) {
            $training &= -65;
            if (in_array('training', $keys))
                $datum['training'] = $training;

            $seq_param_with_inputs[] = [...array_map(fn ($key) => $datum[$key], $keys_rest), $datum[$primary_key]];
        } else {
            if (in_array('training', $keys))
                $datum['training'] = $training;

            if (array_key_exists($table, $datum)) {
                $seq_param[] = [$datum[$table], $datum[$primary_key]];
            } else {
                $seq_param_with_inputs[] = [...array_map(fn ($key) => $datum[$key], $keys_rest), $datum[$primary_key]];
            }
        }

        $data[] = $datum;
    }

    if ($seq_param) {
        $rowcount = mysql\multi_query(array_map(function ($tuple) use ($database, $table, $primary_key, $Field2Type) {
            [$table_value, $table_primary_key] = $tuple;
            $table_value = mysql\mysqlStr($table_value, $Field2Type[$table], false);
            $table_primary_key = mysql\mysqlStr($table_primary_key, $Field2Type[$primary_key], false);
            return "update $database.`$table` set $table = $table_value where $primary_key = $table_primary_key";
        }, $seq_param), false);
    } else
        $rowcount = 0;

    if ($seq_param_with_inputs) {
        $rowcount_text = mysql\multi_query(array_map(function ($key_rest_value) use ($database, $table, $primary_key, $keys_rest, $Field2Type) {
            $primary_key_value = array_pop($key_rest_value);

            $parameters = implode(", ", array_map(fn ($tuple) => $tuple[0] . " = " . mysql\mysqlStr($tuple[1], $Field2Type[$tuple[0]], false), std\zipped($keys_rest, $key_rest_value)));
            return "update $database.`$table` set $parameters where $primary_key = '$primary_key_value'";
        }, $seq_param_with_inputs), false);
    } else {
        $rowcount_text = 0;
    }

    $rowcount += $rowcount_text;

    $primary_keys = array_map(fn ($json) => str_replace("'", "''", $json[$primary_key]), $data);

    if ($rowcount < count($seq_param) + count($seq_param_with_inputs)) {
        if (! $primary_keys) {
            $sql = "select $primary_key from $database.`$table` limit 0";
        } elseif (count($primary_keys) == 1) {
            $sql = "select $primary_key from $database.`$table` where $primary_key = '$primary_keys[0]'";
        } else {
            $primary_keys_str = implode(", ", array_map(fn ($key) => "'$key'", $primary_keys));
            $sql = "select $primary_key from $database.`$table` where $primary_key in ($primary_keys_str)";
        }

        $duplicate_keys = array_map(fn ($tuple) => $tuple[0]?? null, get_rows($sql));
        $seq_param = [];
        foreach ($data as &$json) {
            if (in_array($json[$primary_key], $duplicate_keys)) {
                error_log($json[$primary_key] . ' is duplicated');
                continue;
            }

            $seq_param[] = array_map(fn ($key) => $json[$key], $keys);
        }

        $rowcount += mysql\multi_query(array_map(function ($tuple) use ($database, $table, $Field2Type, $keys) {
            foreach (std\range(count($keys)) as $i) {
                $tuple[$i] = mysql\mysqlStr($tuple[$i], $Field2Type[$keys[$i]], false);
            }

            $parameters = implode(', ', $tuple);
            return "insert into $database.`$table` values ($parameters)";
        }, $seq_param), false);
    }

    error_log('rowcount = ' . $rowcount);

    if (! count($primary_keys)) {
        $sql = "select * from $database.`$table` limit 0";
    } elseif (count($primary_keys) == 1) {
        $sql = "select * from $database.`$table` where $primary_key = '$primary_keys[0]'";
    } else {
        $primary_keys = array_map(fn ($el) => "'$el'", $primary_keys);
        $primary_keys_str = implode(", ", $primary_keys);
        $sql = "select * from $database.`$table` where $primary_key in ($primary_keys_str)";
    }

    mysql\json_decode_by_field_to_type($Field2Type, $data);
}

// error_log("data = ".std\encode($data));
?>