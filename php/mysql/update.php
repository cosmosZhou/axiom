<?php
require dirname(__file__).'/../regexp/SyntaxMatcher.php';
require dirname(__file__).'/../xml/RichText.php';

if ($scanCriteria == null)
    $scanCriteria = [];

if (! $kwargs['limit']) {
    $kwargs['limit'] = '40';
}

function join_condition($conditions, $cond) {
    return $conditions? "$conditions and $cond": $cond; 
}

$set = $kwargs['set'];
$eq = $set['eq'];
$setter = $eq[0];

$sql_select = "select * from ${database}.${table} ";
[$Field2Type, $primary_key, $indexKey, $transform] = mysql\field_to_type($database, $table);

if (is_string($eq[1])) {
    $functor = '';
}
else {
    [$functor] = array_keys($eq[1]);
    $scanCriteria = search_for_scan_criteria($kwargs, $Field2Type, $primary_key, $transform);
}

$conditions = parse_expression($kwargs['where'], $Field2Type, $transform, $scanCriteria);

switch ($functor) {
case 'regexp_replace':
    [[$setter, $old, $new]] = array_values($eq[1]);
    if (count($scanCriteria) > 1) {
        [$old, $new, , $binary] = $scanCriteria[0][1];
    } else {
        $fn = $transform[$setter];
        if ($fn) {
            $fn = "transform_$transform[$setter]";
            [$old, $new, $binary] = $fn($old, $new);
        }
        else {
            $new = preg_replace("/[\\\\](\d+)/", '$$1', $new);
            $new = mysql\mysqlStr($new, '', false);
        }
    }

    // error_log("after transforming");
    // error_log("\$old = ".$old);
    // error_log("\$new = ".$new);
    $old_mysql = mysql\mysqlStr($old);
    $match_parameter = $binary ? ", 1, 0, 'c'" : '';

    if (! $match_parameter) {
        if ($operator = std\get($kwargs, 'operator', [])) {
            if ($regexp_replace = std\get($operator, 'regexp_replace')) {
                if ($modifier = std\get($regexp_replace, $setter)) {
                    $match_parameter = ", 1, 0, '$modifier'";
                    $binary = $modifier == 'c';
                }
            }
        }
    }

    $sql_update = "update ${database}.${table} set $setter = $functor($setter, $old_mysql, '$new'$match_parameter) ";

    if ($binary) {
        $cond = "regexp_like($setter, $old_mysql, 'c')";
        if (! std\contains($conditions, $cond)) {
            $conditions = join_condition($conditions, $cond);
        }
    }
    else {
        if (! preg_match("/\\b$setter regexp /", $conditions)) {
            $conditions = join_condition($conditions, "$setter regexp $old_mysql");
        }
    }

    break;

case 'replace':
    [[$setter, $old, $new]] = array_values($eq[1]);
    $sql_update = "update ${database}.${table} set $setter = $functor($setter, '$old', '$new') ";
    $conditions = join_condition($conditions, "$setter regexp '$old'");
    break;

case 'json_remove':
    [[$setter, $key]] = array_values($eq[1]);
    $sql_update = "update ${database}.${table} set $setter = $functor($setter, '$key') ";
    $conditions = join_condition($conditions, "json_contains_path($setter, 'all', '$key')");
    break;

case 'substring':
    [[$setter, $from, $length]] = array_values($eq[1]);
    if ($length)
        $length = ", $length";
    $sql_update = "update ${database}.${table} set $setter = $functor($setter, $from$length) ";
    break;
    
default:
    if ($functor) {
        $sql_update = "update ${database}.${table} set $setter = $functor($setter) ";
        $conditions = join_condition($conditions, "binary $setter != $functor($setter)");
    } else {
        $new = $eq[1];
        if (mysql\is_number($Field2Type[$setter])) {
            $sql_update = "update ${database}.${table} set $setter = $new ";
            $conditions = join_condition($conditions, "$setter != $new");
        } else if ($scanCriteria) {} else {
            $_new = str_replace('\\', '\\\\', $new);
            $sql_update = "update ${database}.${table} set $setter = '$_new' ";
            $conditions = join_condition($conditions, "binary $setter != '$new'");
        }
    }
    break;
}

if ($conditions)
    $sql_select .= "where $conditions";

$order = $kwargs['order'];
if ($order) {
    if (is_array($order)) {
        [$order, $desc] = $order;
        if ($order) {
            $sql_select .= " order by $order";
            if ($desc) {
                $sql_select .= " $desc";
            }
        }
    }
}
    

if (count($scanCriteria) == 1) {
    if (! $functor && ! mysql\is_number($Field2Type[$setter])) {
        $scanCriteria[] = [$setter, '!=', $new];
    }
}

if (count($scanCriteria) > 1) {
    scan_data($sql_select, $Field2Type, $scanCriteria, $kwargs, $primary_key, true);
    [[$textField, [$regexp, $indexCaptured]], [$entityField, $op, $entityValue]] = $scanCriteria;

    $sql_update = [];
    foreach ($data as &$inst) {
        $primary_key_value = mysql\mysqlStr($inst[$primary_key]);

        $setterValueStr = $inst[$setter];
        if (mysql\is_json($Field2Type[$setter])) {
            $setterValueStr = std\encode($setterValueStr);
        }

        $setterValueStr = mysql\mysqlStr($setterValueStr, $Field2Type[$setter]);

        $sql_update[] = "update ${database}.${table} set $setter = $setterValueStr where $primary_key = $primary_key_value";

        $training = array_key_exists('training', $inst) ? (int)$inst['training'] : 0;

        if ($setter != $table)
            $training |= 64;

        $inst['training'] = ~ $training;
    }
    // $sql_replace = array_map(fn ($args) => "($args[0], $args[1])");
    $sql = implode(";\n", $sql_update);
} else {
    $limit = $kwargs['limit'];
    if ($limit)
        $sql_select .= " limit $limit";

    $offset = $kwargs['offset'];
    if ($offset)
        $sql_select .= " offset $offset";

    $sql = $sql_select;
    load_data($sql, $Field2Type);

    if ($order || $offset) {
        $sql_select = str_replace('select * ', "select $primary_key ", $sql_select);
        $sql_select = trim($sql_select);

        if ($limit)
            $sql_select = "select _$table.$primary_key from ($sql_select) as _$table";

        $sql_update .= "where $primary_key in ($sql_select) ";
    } else {
        if ($conditions)
            $sql_update .= "where $conditions ";

        if ($limit)
            $sql_update .= "limit $limit ";
    }

    switch ($functor) {
    case 'regexp_replace':
        $new = std\decode("\"$new\"");
        $oldRegex = wrap_regexp($old, $binary ? '' : 'i');
        $functor = fn ($arg) => preg_replace($oldRegex, $new, $arg);
        break;
        
    case 'replace':
        $new = std\decode("\"$new\"");
        $functor = fn ($arg) => str_replace($old, $new, $arg);
        break;
        
    case 'json_remove':
        $functor = function &(&$arg) use ($key) {
            std\json_remove($arg, $key);
            return $arg;
        };
        break;
        
    case 'substring':
        $from = (int)$from - 1;
        $functor = function (&$arg) use ($from, $length) {
            if ($length)
                return std\substring($arg, $from, $from + $length);
            else
                return std\substring($arg, $from);
        };
        break;
        
    case 'lower':
        $functor = fn ($arg) => strtolower($arg);
        break;
        
    case 'upper':
        $functor = fn ($arg) => strtoupper($arg);
        break;
        
    case '':
        if (mysql\is_int($Field2Type[$setter])) {
            $functor = fn ($arg) => (int)$new;
        } elseif (mysql\is_float($Field2Type[$setter])) {
            $functor = fn ($arg) => (float)$new;
        } else {
            $functor = fn ($arg) => $new;
        }
        break;
        
    default:
        error_log("unknown functor detected $functor");
        break;
    }

    $sql = $sql_update;
    foreach ($data as &$inst) {
        $inst[$setter] = $functor($inst[$setter]);
        if (mysql\is_json($Field2Type[$setter]) && is_string($inst[$setter])) {
            $inst[$setter] = std\decode($inst[$setter]);
        }

        $training = array_key_exists('training', $inst) ? (int)$inst['training'] : 0;

        if ($setter != $table)
            $training |= 64;

        $inst['training'] = ~ $training;
    }
}
?>