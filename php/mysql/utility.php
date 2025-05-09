<?php

function wrap_regexp($regexp, $i)
{
    global $database, $table;
    if ($i)
        $i = mysql\is_collation_case_insensitive($database, $table) ? 'i' : '';

    $u = 'u';
    foreach (std\iter("/`#%~@$^&*!-_=+?\\|;:'\"()[]{}<>,.") as $ch) {
        if (! std\contains($regexp, $ch))
            return "$ch$regexp$ch$u$i";
    }
}

function scan_syntax_with_entity($text, &$syntax, &$entity, $regexp, $indexCaptured, $op, $type, $replacement = null, $update = false)
{
    $entity = std\decode($entity);
    $hit = false;

    $syntaxStart = 0;
    $buffer = [];
    $matches = std\matchAll($regexp, $syntax, $indexCaptured);
    if (! $matches)
        return false;

    $physicalTextInSyntax = [];
    $logicalTexts = [];
    $segments = [];
    foreach (std\matchAll("/[^{}]+/u", $syntax) as [&$m, $offsetStart]) {
        $physicalTextInSyntax[] = ['start' => $offsetStart, 'end' => $offsetStart + std\len($m[0])];
        $segments[] = $m[0];
    }

    $richText = construct_rich_text($text);
    if (! $richText) {
        error_log("construct_rich_text($text) returning null?");
        return false;
    }

    $logicalOffset = $richText->getLogicalIndices($segments);
    if (! $logicalOffset)
        return false;

    array_pop($indexCaptured);

    foreach ($matches as [&$match, &$indices]) {
        $syntaxIndex = array_pop($indices);
        if ($syntaxStart < $syntaxIndex && $update)
            $buffer[] = std\slice($syntax, $syntaxStart, $syntaxIndex);

        $matchAll = true;

        foreach (std\enumerate($indexCaptured) as [$t, $i]) {
            $offsetStart = $indices[$t];
            $offsetEnd = $offsetStart + std\len($match[$i]);
            $physicalText = ['start' => $offsetStart, 'end' => $offsetEnd];

            $index = std\binary_search($physicalTextInSyntax, $physicalText, 'std\range_cmp');

            [$offsetStart, $offsetEnd] = $richText->getPhysicalIndices(...$logicalOffset[$index]);
            $pivot = ['start' => $offsetStart, 'end' => $offsetEnd];
            $index = std\binary_search($entity, $pivot, 'std\range_cmp');

            if ($index < count($entity) && $entity[$index]['start'] < $offsetEnd) {
                $targetType = $entity[$index]['type'];
            } else {
                $targetType = 'null';
            }

            if (($op == '=') ^ ($targetType == $type)) {
                $matchAll = false;
                break;
            }
        }

        if ($matchAll) {
            if (! $update) {
                $hit = true;
                break;
            }

            $buffer[] = preg_replace_callback("/\\$(\d+)/", fn (&$m) => $match[(int)$m[1]], $replacement);

            $hit = true;
        } else {
            if ($update)
                $buffer[] = $match[0];
        }

        $syntaxStart = $syntaxIndex + std\len($match[0]);
    }

    if ($hit && $update) {
        $buffer[] = std\slice($syntax, $syntaxStart);
        $syntax = implode('', $buffer);
    }

    return $hit;
}

function scan_syntax_with_text($text, &$syntax, $regexp, $indexCaptured, $op, $textRegexp, $replacement = null, $update = false)
{
    $hit = false;

    $syntaxStart = 0;
    $buffer = [];
    $matches = std\matchAll($regexp, $syntax, $indexCaptured);
    if (! $matches)
        return false;

    $physicalTextInSyntax = [];
    $logicalTexts = [];
    $segments = [];
    foreach (std\matchAll("/[^{}]+/u", $syntax) as [&$m, $offsetStart]) {
        $physicalTextInSyntax[] = ['start' => $offsetStart, 'end' => $offsetStart + std\len($m[0])];
        $segments[] = $m[0];
    }

    $richText = construct_rich_text($text);
    if (! $richText) {
        error_log("construct_rich_text($text) returning null?");
        return false;
    }

    $logicalOffset = $richText->getLogicalIndices($segments);
    if (! $logicalOffset)
        return false;

    $entity = [];
    $groupCount = count($indexCaptured);
    foreach (std\matchAll($textRegexp, $text, std\ranged($groupCount)) as [&$m, &$indices]) {
        $start = $indices[0];
        $end = $start + std\len($m[0]);

        $group = [];
        foreach (std\range(1, $groupCount) as $i) {
            $offsetStart = $indices[$i];
            $offsetEnd = $offsetStart + std\len($m[$i]);
            $group[] = ['start' => $offsetStart, 'end' => $offsetEnd];
        }

        $entity[] = ['start' => $start, 'end' => $end, 'text' => $m[0], 'group' => $group];
    }

    array_pop($indexCaptured);

    foreach ($matches as [&$match, &$indices]) {
        $syntaxIndex = array_pop($indices);
        if ($syntaxStart < $syntaxIndex && $update)
            $buffer[] = std\slice($syntax, $syntaxStart, $syntaxIndex);

        $matchAll = true;
        foreach (std\enumerate($indexCaptured) as [$t, $i]) {
            $offsetStart = $indices[$t];
            $offsetEnd = $offsetStart + std\len($match[$i]);
            $physicalText = ['start' => $offsetStart, 'end' => $offsetEnd];

            $index = std\binary_search($physicalTextInSyntax, $physicalText, 'std\range_cmp');

            [$offsetStart, $offsetEnd] = $richText->getPhysicalIndices(...$logicalOffset[$index]);
            $pivot = ['start' => $offsetStart, 'end' => $offsetEnd];

            $index = std\binary_search($entity, $pivot, 'std\range_cmp');

            $groupOffsets = $entity[$index]['group'][$t];

            if ($index < count($entity) && $entity[$index]['start'] < $offsetEnd && (new std\Range($offsetStart, $offsetEnd))->contains(new std\Range($groupOffsets['start'], $groupOffsets['end']))) {
                if ($groupIndex === null) {
                    $groupIndex = $index;
                } elseif ($groupIndex != $index) {
                    $matchAll = false;
                    break;
                }
            } else {
                $matchAll = false;
                break;
            }
        }

        if ($matchAll) {
            if (! $update) {
                $hit = true;
                break;
            }

            $buffer[] = preg_replace_callback("/\\$(\d+)/", fn (&$m) => $match[(int)$m[1]], $replacement);

            $hit = true;
        } else {
            if ($update)
                $buffer[] = $match[0];
        }

        $syntaxStart = $syntaxIndex + std\len($match[0]);
    }

    if ($hit && $update) {
        $buffer[] = std\slice($syntax, $syntaxStart);
        $syntax = implode('', $buffer);
    }

    return $hit;
}

function scan_text_with_entity($text, &$entity, $regexp, $indexCaptured, $op, $type, $newType = null, $update = false)
{
    $entity = std\decode($entity);
    $hit = false;
    $matchAll = is_int($update) ? 'std\matchAllExtended' : 'std\matchAll';
    foreach ($matchAll($regexp, $text, $indexCaptured) as &$args) {
        [&$match, $newStart] = $args;
        $textPiece = $match[$indexCaptured];
        $newEnd = $newStart + std\len($textPiece);

        while (std\get($text, $newStart) == ' ') {
            ++ $newStart;
        }

        while (std\get($text, $newEnd - 1) == ' ') {
            -- $newEnd;
        }

        $newEntity = ['start' => $newStart, 'end' => $newEnd, 'type' => $newType];

        [$index, $indexEnd] = std\equal_range($entity, $newEntity, 'std\range_cmp');
        $size = $indexEnd - $index;
        if (! $size) {
            $oldType = 'null';
            if (($op == '=') ^ ($oldType == $type)) {
                continue;
            }

            if ($newType) {
                if ($newType == 'null') {
                    continue;
                }

                if (! $update) {
                    if ($op != '=' && $newType == $oldType)
                        continue;
                    $hit = true;
                    break;
                }

                if ($index < count($entity) && $entity[$index]['start'] == $newEnd && $newType == $entity[$index]['type']) {
                    if ($index && $entity[$index - 1]['end'] == $newStart && $newType == $entity[$index - 1]['type']) {
                        $entity[$index - 1]['end'] = $entity[$index]['end'];
                        std\array_delete($entity, $index);
                    } else {
                        $entity[$index]['start'] = $newStart;
                    }
                } else if ($index && $entity[$index - 1]['end'] == $newStart && $newType == $entity[$index - 1]['type']) {
                    $entity[$index - 1]['end'] = $newEnd;
                } else {
                    std\array_insert($entity, $index, $newEntity);
                }

                $hit = true;
            } else {
                $hit = true;
                break;
            }
        } elseif ($size == 1) {
            $oldEntity = &$entity[$index];
            $oldStart = $oldEntity['start'];
            $oldEnd = $oldEntity['end'];

            $oldType = $oldEntity['type'];
            if ($oldStart > $newStart) {
                if ($newType) {
                    if ($oldEnd < $newEnd) {
                        if ($type == 'null') {
                            if ($op == '=') {
                                if ($newType == 'null') {} elseif ($newType == $oldType) {
                                    if (! $update) {
                                        $hit = true;
                                        break;
                                    }

                                    $oldEntity['end'] = $newEnd;
                                    if ($index + 1 < count($entity)) {
                                        $nextEntity = &$entity[$index + 1];
                                        if ($newType == $nextEntity['type'] && $nextEntity['start'] == $newEnd) {
                                            $oldEntity['end'] = $nextEntity['end'];
                                            std\array_delete($entity, $index + 1);
                                            $oldEntity = &$entity[$index];
                                        }
                                    }

                                    $oldEntity['start'] = $newStart;
                                    if ($index) {
                                        $prevEntity = &$entity[$index - 1];
                                        if ($newType == $prevEntity['type'] && $prevEntity['end'] == $newStart) {
                                            $prevEntity['end'] = $oldEntity['end'];
                                            std\array_delete($entity, $index);
                                        }
                                    }

                                    $hit = true;
                                }
                            } else {
                                if ($newType == 'null') {
                                    if (! $update) {
                                        $hit = true;
                                        break;
                                    }
                                    std\array_delete($entity, $index);
                                    $hit = true;
                                }
                            }
                        }
                    } elseif ($oldEnd > $newEnd) {
                        // skipping;
                    } else {
                        if ($type == 'null') {
                            if ($op == '=') {
                                if ($newType == 'null') {} elseif ($newType == $oldType) {
                                    if (! $update) {
                                        $hit = true;
                                        break;
                                    }

                                    $oldEntity['start'] = $newStart;
                                    if ($index) {
                                        $prevEntity = &$entity[$index - 1];
                                        if ($newType == $prevEntity['type'] && $prevEntity['end'] == $newStart) {
                                            $prevEntity['end'] = $newEnd;
                                            std\array_delete($entity, $index);
                                        }
                                    }

                                    $hit = true;
                                }
                            } else {
                                if ($newType == 'null') {
                                    if (! $update) {
                                        $hit = true;
                                        break;
                                    }

                                    std\array_delete($entity, $index);
                                    $hit = true;
                                }
                            }
                        }
                    }
                }
            } elseif ($oldEnd < $newEnd) {
                // $oldStart <= $newStart
                if ($newType) {
                    if ($op == '=') {
                        if ($type == 'null') {
                            if ($newType == 'null') {} elseif ($newType == $oldType) {
                                if (! $update) {
                                    $hit = true;
                                    break;
                                }

                                $oldEntity['end'] = $newEnd;
                                if ($index + 1 < count($entity)) {
                                    $nextEntity = &$entity[$index + 1];
                                    if ($newType == $nextEntity['type'] && $nextEntity['start'] == $newEnd) {
                                        $entity[$index]['end'] = $nextEntity['end'];
                                        std\array_delete($entity, $index + 1);
                                    }
                                }

                                $hit = true;
                            }
                        }
                    } else {
                        if ($oldStart < $newStart) {
                            // skipping;
                        } else {
                            if ($newType != 'null') {
                                if (! $update) {
                                    $hit = true;
                                    break;
                                }

                                if ($newType != $oldType) {
                                    $oldEntity['type'] = $newType;
                                }

                                $oldEntity['end'] = $newEnd;
                                if ($index + 1 < count($entity)) {
                                    $nextEntity = &$entity[$index + 1];
                                    if ($newType == $nextEntity['type'] && $nextEntity['start'] == $newEnd) {
                                        $entity[$index]['end'] = $nextEntity['end'];
                                        std\array_delete($entity, $index + 1);
                                    }
                                }

                                $hit = true;
                            }
                        }
                    }
                }
            } else {
                if (($op == '=') ^ ($oldType == $type)) {
                    continue;
                }
                // $oldStart <= $newStart && $oldEnd >= $newEnd

                // now that $oldType != null:
                if (! $update) {
                    if ($op != '=' && $newType == $oldType)
                        continue;
                    $hit = true;
                    break;
                }

                if ($newType) {

                    if ($newType == 'null') {
                        // error_log("old entity = ".std\encode($oldEntity));
                        // error_log("delete region = ".std\encode($newEntity));
                        if ($newStart > $oldStart) {
                            $oldEntity['end'] = $newStart;
                            while (std\get($text, $oldEntity['end'] - 1) == ' ') {
                                -- $oldEntity['end'];
                            }

                            if ($newEnd < $oldEnd) {
                                $newEntity['start'] = $newEntity['end'];
                                $newEntity['end'] = $oldEnd;
                                $newEntity['type'] = $oldEntity['type'];
                                while (std\get($text, $newEntity['start']) == ' ') {
                                    ++ $newEntity['start'];
                                }

                                std\array_insert($entity, $index + 1, $newEntity);
                            }
                        } else {
                            // $newStart == $oldStart
                            $oldEntity['start'] = $newEnd;
                            if ($oldEntity['start'] < $oldEntity['end']) {
                                while (std\get($text, $oldEntity['start']) == ' ') {
                                    ++ $oldEntity['start'];
                                }
                            } else {
                                std\array_delete($entity, $index);
                            }
                        }
                    } else {
                        if ($oldType == $newType) {
                            continue;
                        }
                        // error_log("old entity = ".std\encode($oldEntity));
                        // error_log("delete region = ".std\encode($newEntity));

                        if ($newStart > $oldStart) {
                            $oldEntity['end'] = $newStart;
                            while (std\get($text, $oldEntity['end'] - 1) == ' ') {
                                -- $oldEntity['end'];
                            }

                            if ($newEnd < $oldEnd) {
                                std\array_insert($entity, $index + 1, $newEntity);

                                $newEntity['start'] = $newEntity['end'];
                                $newEntity['end'] = $oldEnd;
                                $newEntity['type'] = $oldEntity['type'];
                                while (std\get($text, $newEntity['start']) == ' ') {
                                    ++ $newEntity['start'];
                                }

                                std\array_insert($entity, $index + 2, $newEntity);
                            } else {
                                std\array_insert($entity, $index + 1, $newEntity);
                            }
                        } else {
                            if ($newEnd < $oldEntity['end']) {
                                $oldEntity['start'] = $newEnd;
                                while (std\get($text, $oldEntity['start']) == ' ') {
                                    ++ $oldEntity['start'];
                                }

                                std\array_insert($entity, $index, $newEntity);
                            } else {
                                $oldEntity['type'] = $newType;

                                if ($index + 1 < count($entity)) {
                                    $nextEntity = &$entity[$index + 1];
                                    if ($newType == $nextEntity['type'] && $nextEntity['start'] == $newEnd) {
                                        $entity[$index]['end'] = $nextEntity['end'];
                                        std\array_delete($entity, $index + 1);
                                    }
                                }
                            }

                            if ($index) {
                                $prevEntity = &$entity[$index - 1];
                                if ($newType == $prevEntity['type'] && $prevEntity['end'] == $newStart) {
                                    $prevEntity['end'] = $newEnd;
                                    std\array_delete($entity, $index);
                                }
                            }
                        }
                    }

                    $hit = true;
                }
            }
        } else {
            if (! $newType) {
                continue;
            }

            $oldType = [];
            foreach (std\range($index, $indexEnd) as $i) {
                $oldType[$entity[$i]['type']] = true;
            }

            if (count($oldType) > 1) {
                if ($op != '=') {
                    if ($newType != 'null') {

                        if (! $update) {
                            $hit = true;
                            break;
                        }

                        if ($entity[$index]['start'] < $newStart) {
                            $newStart = $entity[$index]['start'];
                        }

                        if ($entity[$indexEnd - 1]['end'] > $newEnd) {
                            $newEnd = $entity[$indexEnd - 1]['end'];
                        }

                        array_splice($entity, $index, $size - 1);
                        $oldEntity = &$entity[$index];
                        $oldEntity['type'] = $newType;

                        $oldEntity['end'] = $newEnd;
                        if ($index + 1 < count($entity)) {
                            $nextEntity = &$entity[$index + 1];
                            if ($newType == $nextEntity['type'] && $nextEntity['start'] == $newEnd) {
                                $entity[$index]['end'] = $nextEntity['end'];
                                std\array_delete($entity, $index + 1);
                                $oldEntity = &$entity[$index];
                            }
                        }

                        if ($oldEntity['start'] > $newStart) {
                            $oldEntity['start'] = $newStart;
                            if ($index) {
                                $prevEntity = &$entity[$index - 1];
                                if ($newType == $prevEntity['type'] && $prevEntity['end'] == $newStart) {
                                    $prevEntity['end'] = $newEnd;
                                    std\array_delete($entity, $index);
                                }
                            }
                        }

                        $hit = true;
                    }
                } else
                    continue;
            } else {
                [$oldType] = array_keys($oldType);
                if ($type == 'null' && $newType == $oldType) {
                    if (! $update) {
                        $hit = true;
                        break;
                    }

                    if ($entity[$index]['start'] < $newStart) {
                        $newStart = $entity[$index]['start'];
                    }

                    if ($entity[$indexEnd - 1]['end'] > $newEnd) {
                        $newEnd = $entity[$indexEnd - 1]['end'];
                    }

                    array_splice($entity, $index, $size - 1);
                    $oldEntity = &$entity[$index];

                    $oldEntity['end'] = $newEnd;
                    if ($index + 1 < count($entity)) {
                        $nextEntity = &$entity[$index + 1];
                        if ($newType == $nextEntity['type'] && $nextEntity['start'] == $newEnd) {
                            $entity[$index]['end'] = $nextEntity['end'];
                            std\array_delete($entity, $index + 1);
                            $oldEntity = &$entity[$index];
                        }
                    }

                    if ($oldEntity['start'] > $newStart) {
                        $oldEntity['start'] = $newStart;
                        if ($index) {
                            $prevEntity = &$entity[$index - 1];
                            if ($newType == $prevEntity['type'] && $prevEntity['end'] == $newStart) {
                                $prevEntity['end'] = $newEnd;
                                std\array_delete($entity, $index);
                            }
                        }
                    }

                    $hit = true;
                }
            }
        }
    }

    return $hit;
}

function scan_data($sql, &$Field2Type, $kwargs, $update = false)
{
    $scanCriteria = $Field2Type['__scan_criteria__'];
    $primary_key = $Field2Type['__primary_key__'];
    global $data;
    if (preg_match("/(.+)( limit \d+)( offset \d+)?/", $sql, $m)) {
        $sql = $m[1];
    }

    $limit = $kwargs['limit'];
    $limit = (int)$limit;

    $offset = $kwargs['offset'];
    $offset = $offset ? (int)$offset : 0;

    $sql_scan = "$sql limit {$limit}0000 offset $offset";

    error_log("scanning with sql = " . $sql_scan);

    if (count(end($scanCriteria)) == 3) {
        if (preg_match("/regexp/", end($scanCriteria)[1])) {
            [[$syntaxField, [$regexp, $new, $indexCaptured, $binary], $i], [$textField, $op, [$textRegexp, $indexCapturedForText, $binaryForText]]] = $scanCriteria;
            $regexp = wrap_regexp($regexp, $i);
            $textRegexp = wrap_regexp($textRegexp, $i);

            $data = mysql\scan_data($sql_scan, True, fn (&$data) => scan_syntax_with_text($data[$textField], $data[$syntaxField], $regexp, $indexCaptured, $op, $textRegexp, $new, $update), $limit, $offset);
        } else {
            [[$textField, [$regexp, $new, $indexCaptured], $i], [$entityField, $op, $entityValue]] = $scanCriteria;
            $regexp = wrap_regexp($regexp, $i);

            global $anyRegexp;
            if (std\fullmatch("/\(\?:\^\(\?:\(\?!$anyRegexp\(\?:($anyRegexp)\)\)\.\)\*\?\)\(\\1\)/", std\substring($regexp, 1, strrpos($regexp, $regexp[0])))) {
                $update = $update ? 1 : 0;
            }

            $data = mysql\scan_data($sql_scan, True, fn (&$data) => scan_text_with_entity($data[$textField], $data[$entityField], $regexp, $indexCaptured, $op, $entityValue, $new, $update), $limit, $offset);
        }
    } elseif (count(end($scanCriteria)) == 4) {
        [[$syntaxField, [$regexp, $new, $indexCaptured, $binary], $i], [$entityField, $op, $entityValue, $textField]] = $scanCriteria;
        $regexp = wrap_regexp($regexp, $i);

        $data = mysql\scan_data($sql_scan, True, fn (&$data) => scan_syntax_with_entity($data[$textField], $data[$syntaxField], $data[$entityField], $regexp, $indexCaptured, $op, $entityValue, $new, $update), $limit, $offset);
    }

    $kwargs['offset'] = [$kwargs['offset'], $offset];
    mysql\json_decode_by_field_to_type($Field2Type, $data);
    $primary_keys = array_map(fn (&$data) => $data[$primary_key], $data);

    global $database, $table;
    if (! $primary_keys) {
        $sql = "select * from $database.$table limit 0";
    } elseif (count($primary_keys) == 1) {
        $sql = "select * from $database.$table where $primary_key = '$primary_keys[0]'";
    } else {
        $primary_keys_str = implode(", ", array_map(fn ($key) => "'$key'", $primary_keys));
        $sql = "select * from $database.$table where $primary_key in ($primary_keys_str)";
    }

    return $sql;
}

function sample()
{
    global $data, $kwargs, $order;
    $sample = std\get($kwargs, 'sample');
    if ($sample) {
        $length = count($data);
        $sample = (float)$sample;
        if ($sample < 1)
            $count = floor($sample * $length);
        else
            $count = (int)$sample;

        if ($count)
            $data = $order == 'rand()' ? std\sample($data, $count) : std\slice($data, 0, $length, (int)($length / $count));
    }
}

function load_data($sql, $Field2Type = null, $json_decode = true)
{
    global $data;
    $data = get_rows($sql);
    if ($json_decode && $Field2Type)
        mysql\json_decode_by_field_to_type($Field2Type, $data);
}

function piece_together($Field, $where_dict, &$transform)
{
    [$operator, $value] = $where_dict[$Field];
    $value = functional_substitution($value);

    $binary = null;
    if ($transform[$Field]) {
        $fn = "transform_$transform[$Field]";
        $list = $fn($value);

        if (count($list) >= 2) {
            [$value, $binary] = $list;
        } else {
            [$value] = $list;
        }
    }
    $indexCaptured = 0;
    /*
     * $is_or_structure = null;
     * $look_ahead_operator = std\getitem($operator, 'look_ahead', $Field);
     * if ($look_ahead_operator) {
     * $look_ahead_value = std\getitem($kwargs, 'look_ahead', $Field);
     * if ($look_ahead_value) {
     * $look_ahead_value = functional_substitution($look_ahead_value);
     * if (Regex::compile($value)->is_or_structure()) {
     * $value = "(?:$value)";
     * $is_or_structure = false;
     * }
     * $value = "$value(?$look_ahead_operator$look_ahead_value)";
     * }
     * }
     *
     * $look_behind_operator = std\getitem($operator, 'look_behind', $Field);
     *
     * if ($look_behind_operator) {
     * $look_behind_value = std\getitem($kwargs, 'look_behind', $Field);
     * if ($look_behind_value) {
     * $look_behind_value = functional_substitution($look_behind_value);
     * if (Regex::compile($look_behind_value)->match_length() === null) {
     * // error_log("\$look_behind_value = " . $look_behind_value);
     * $look_behind_value = remove_capture($look_behind_value);
     *
     * if ($look_behind_operator == '!') {
     * $lookahead = "(?!$look_behind_value(?:$value))";
     * // there is no character which is prepended with $look_behind_value before $value;
     * // $look_behind_value = "^(?:.$lookahead)*|^$lookahead";
     * $look_behind_value = "^(?:$lookahead.)*?";
     * }
     *
     * $value = "(?:$look_behind_value)($value)";
     * $indexCaptured = 1;
     * } else {
     * // error_log("is not variable_length");
     * if ($is_or_structure === null && Regex::compile($value)->is_or_structure())
     * $value = "(?:$value)";
     *
     * $value = "(?<$look_behind_operator$look_behind_value)$value";
     * }
     * }
     * }
     */
    return [$value, $indexCaptured, $binary];
}

function look_behind_adjustment($regexp, $transform_fn) {
    $regexObj = Regex::compile($regexp, $transform_fn);
    $regexObj->rewrite($transform_fn);
    return "$regexObj";
}

function get_where_dict(&$kwargs)
{
    $where_dict = [];
    $where = std\get($kwargs, 'where', []);
    $and = std\get($where, 'and', []);
    foreach ($and as &$cond) {
        [[$operator, $operands]] = std\entries($cond);

        if (is_string($operands[0])) {
            $where_dict[$operands[0]] = [$operator, $operands[1]];
        }
    }
    return $where_dict;
}

function search_for_entity_field(&$where_dict, &$Field2Type)
{
    foreach ($where_dict as $Field => [$operator, $operand]) {
        if ($operand && ($operator == '=' || $operator == '!=') && mysql\is_json($Field2Type[$Field]) && $Field2Type['__transform__'][$Field] == 'entity')
            return $Field;
    }
}

function search_for_text_field(&$where_dict, &$Field2Type)
{
    $primary_key = $Field2Type['__primary_key__'];
    foreach ($where_dict as $Field => [$operator, $operand]) {
        if ($operand && preg_match("/regexp/", $operator)) {

            if ($Field == $primary_key) {
                continue;
            }

            if (mysql\is_varchar($Field2Type[$Field]) && ! $Field2Type['__transform__'][$Field])
                return $Field;
        }
    }
}

function search_for_syntax_field(&$set, &$where_dict, &$transform)
{
    if (! $transform)
        return;

    if ($set && array_key_exists('eq', $set)) {
        [$setter, $rhs] = $set['eq'];
        [$functor] = array_keys($rhs);
    }

    foreach ($transform as $Field => $fn) {
        if ($fn == 'infix') {
            [$operator, $operand] = $where_dict[$Field];
            if ($operand && preg_match("/regexp/", $operator) || $setter == $Field && $functor == 'regexp_replace')
                return $Field;
        }
    }
}

function search_for_scan_criteria(&$kwargs, &$Field2Type)
{
    $where_dict = get_where_dict($kwargs);
    $entityField = search_for_entity_field($where_dict, $Field2Type);
    $textField = search_for_text_field($where_dict, $Field2Type);
    if (($set = $kwargs['set']?? null) && array_key_exists('eq', $set)) {
        [$setter, $rhs] = $set['eq'];
        [$functor] = array_keys($rhs);
        [$setter, $old, $new] = $rhs[$functor];
    }

    $transform = $Field2Type['__transform__'];
    $scanCriteria = [];
    if ($syntaxField = search_for_syntax_field($set, $where_dict, $Field2Type)) {
        if ($entityField || $textField) {
            if (preg_match("/^varchar\(\\d+\)$/", $Field2Type[$syntaxField], $m)) {
                if ($where_dict[$syntaxField]) {
                    [$operator, $operand] = $where_dict[$syntaxField];
                    if (! $operand)
                        $operand = $old;

                    if (preg_match('/regexp/', $operator)) {
                        if ($operator == 'regexp_like') {
                            $regexp_like = std\get($operator, 'regexp_like');
                            $modifier = $regexp_like ? std\get($regexp_like, $syntaxField) : '';
                            $i = $modifier == 'c' ? '' : 'i';
                        } else {
                            $i = preg_match('/binary/', $operator) ? '' : 'i';
                        }

                        $func = "transform_$transform[$syntaxField]";
                        $scanCriteria[] = [$syntaxField, $func($operand, $new, true), $i];
                    }
                } elseif ($setter == $syntaxField && $functor == 'regexp_replace') {
                    $regexp_replace = std\get($operator, 'regexp_replace');
                    $modifier = $regexp_replace ? std\get($regexp_replace, $syntaxField) : '';
                    $i = $modifier == 'c' ? '' : 'i';

                    $fn = "transform_$transform[$syntaxField]";
                    $scanCriteria[] = [$syntaxField, $fn($old, $new, true), $i];
                }
            }
        }

        if ($scanCriteria) {
            if ($textField) {
                global $leftParenthesisForCapture;
                $syntaxRegex = $old ?? $where_dict[$syntaxField][1];
                if (count(std\matchAll("/$leftParenthesisForCapture/u", $syntaxRegex)) == count(std\matchAll("/$leftParenthesisForCapture/u", $where_dict[$textField][1]))) {
                    $scanCriteria[] = [$textField, $where_dict[$textField][0], piece_together($textField, $where_dict, $transform)];
                }
            } else if ($entityField) {

                foreach ($operator as $textField => $op) {
                    if (is_array($op))
                        continue;

                    if (preg_match("/regexp/", $op) && mysql\is_varchar($Field2Type[$textField]) && ! $transform[$textField] && $Field2Type[$textField] != $primary_key)
                        break;
                }

                $scanCriteria[] = [$entityField, $operator[$entityField], $kwargs[$entityField], $textField];
            }
        }
    } elseif ($entityField) {
        if ($textField) {
            if (preg_match("/^varchar\(\\d+\)$/", $Field2Type[$textField], $m)) {
                if (std\get($kwargs, $textField)) {

                    $op = $operator[$textField];
                    if (preg_match('/regexp/', $op)) {
                        if ($op == 'regexp_like') {
                            $regexp_like = std\get($operator, 'regexp_like');
                            $modifier = $regexp_like ? std\get($regexp_like, $textField) : '';
                            $i = $modifier == 'c' ? '' : 'i';
                        } else {
                            $i = preg_match('/binary/', $op) ? '' : 'i';
                        }

                        [$value, $indexCaptured, $binary] = piece_together($textField, $kwargs, $transform);
                        $scanCriteria[] = [$textField, [$value, $new, $indexCaptured, $binary], $i];
                    }
                }
            }

            if ($scanCriteria) {
                $scanCriteria[] = [$entityField, $operator[$entityField], $kwargs[$entityField]];
            }
        }
    }

    return $Field2Type['__scan_criteria__'] = $scanCriteria;
}

$physic2logic = [
    'eq' => '=',
    'ne' => '!=',
    'gt' => '>',
    'lt' => '<',
    'ge' => '>=',
    'le' => '<=',
    'invert' => '~',
    'add' => '+',
    'sub' => '-',
    'mul' => '*',
    'div' => '/',
    'mod' => '%',
    'dot' => '.',
    'bit_and' => '&',
    'bit_xor' => '^',
    'shr' => '>>',
    'shl' => '<<',
    'json_extract' => '->',
    'json_extract_unquote' => '->>',
    'regexp_binary' => 'regexp binary',
    'like_binary' => 'like binary',
    'not_in' => 'not in',
    'not_regexp' => 'not regexp',
    'not_like' => 'not like',
    'not_regexp_binary' => 'not regexp binary',
    'not_like_binary' => 'not like binary',
    'not_regexp_like' => 'not regexp_like',
    'is_not' => 'is not',
    'union_all' => 'union all'
];


function parse_with(&$with, &$Field2Type, $recursive = false)
{
    $sql = 'with ';
    if ($recursive)
        $sql .= 'recursive ';

    if (std\is_list($with))
        $with = implode(", ", array_map(fn($with) => parse_expression($with, $Field2Type), $with));
    else 
        $with = parse_expression($with, $Field2Type);
    return $sql.$with." ";
}

function parse_statement(&$kwargs, &$Field2Type = null, &$return=null)
{
    $with = $with_recursive = $kwargs['with_recursive']?? null;
    if (!$with)
        $with = $kwargs['with']?? null;
    if ($with) {
        if (std\is_list($with)) {
            $with = parse_with($with, $Field2Type, $with_recursive);
            if ($return)
                $return[$with_recursive? 'with_recursive': 'with'] = $with;
        }
        else {
            [$cte_name, $cte] = $with['as'];
            $Field2Type['__cte__'] = $cte_name;
            if ($with_recursive)
                [$cte, $cte_recursive] = $cte['union']?? $cte['union_all'];

            foreach ($cte['select'] as $field) {
                if (is_array($field)) {
                    if ($as = $field['as']) {
                        [$value, $filed] = $as;
                        $Field2Type[$filed] = mysql\dtype($value);
                    }
                    elseif (is_array($from = $cte['from'])) {
                        if ($cross_join = $from['cross_join']) {
                            if ($as = $cross_join[1]['as']) {
                                [$json_table, $table_name] = $as;
                                if ($json_table = $json_table['json_table']) {
                                    if ($field_name = $field[$table_name]) {
                                        foreach ($json_table[1][1]['columns'] as [$Field, $Type]) {
                                            if ($Field == $field_name) {
                                                if (is_array($Type) && strtolower($Type[0]) == 'for')
                                                    $Type = 'int';
                                                $Field2Type[$Field] = strtolower($Type);
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
    
            $with = parse_with($with, $Field2Type, $with_recursive);
            if ($return)
                $return[$with_recursive? 'with_recursive': 'with'] = $with;
        }
        $sql = $with;    
    }
    else
        $sql = '';

    $from = $kwargs['from'];
    $context = $Field2Type;
    if ($return)
        $context['__desc__'] = $return['__desc__'];
    
    $NewField2Type = mysql\field_to_type($from, $context);
    if ($props = $Field2Type['__props__'])
        preprocess_kwargs($kwargs, $props, $NewField2Type);
    else
        $NewField2Type += $Field2Type;

    if (isset($kwargs['delete'])) {
        $sql .= 'delete';
        $select = '';
    }
    else{
        $select = $kwargs['select'];
        if ($select === null) {
            [[$union_func, $union]] = std\entries($kwargs);
            $statement = array_map(
                function ($kwargs) use ($Field2Type){
                    [$sql] = parse_statement($kwargs, $Field2Type);
                    if ($kwargs['with'] || $kwargs['with_recursive'] || $kwargs['limit'])
                        $sql = "($sql)";
                    return $sql;
                }, 
                $union
            );
            $union_func = str_replace('_', ' ', $union_func);
            return [implode(" $union_func ", $statement), null];
        }
        else {
            $sql .= 'select ';
            $select = std\is_list($select)?
                implode(", ",
                    array_map(
                        fn ($cond) => parse_expression(
                            $cond,
                            $NewField2Type
                        ),
                        $select
                    )
                ):
                parse_expression(
                    $select,
                    $NewField2Type
                );
            if ($return)
                $return['select'] = $select;
        }
    }
    
    $sql .= "$select ";

    if (is_string($from))
        $table = $from;
    elseif (isset($from['from'])) {
        [$statement] = parse_statement($kwargs['from'], $Field2Type);
        $t = get_db_table($kwargs['from'], $Field2Type)[1];
        $table = "($statement) as _$t";
    }
    else
        $table = parse_table($from, $Field2Type);
    if ($return)
        $return['from'] = $table;
    $sql .= "from $table";
    if ($where = parse_expression($kwargs['where'], $NewField2Type)) {
        $sql .= " where $where";
        if ($return)
            $return['where'] = $where;
    }

    if ($group = $kwargs['group']?? null) {
        $group = parse_expression($group, $NewField2Type);
        $sql .= " group by $group";
        if ($return)
            $return['group'] = $group;
    }

    if ($having = std\get($kwargs, 'having', [])) {
        if ($having = parse_expression($having, $NewField2Type)) {
            $sql .= " having $having";
            if ($return)
                $return['having'] = $having;
        }
    }

    if ($order = $kwargs['order']?? null) {
        if (is_string($order));
        elseif (std\is_list($order)) {
            $sort = $order[1]?? null;
            $order = $order[0];
            if ($order) {
                $order = parse_expression($order, $NewField2Type);
                if ($sort)
                    $order .= " $sort";
            }
        } else
            $order = parse_expression($order, $NewField2Type);
        if ($order) {
            $sql .= " order by $order";
            if ($return)
                $return['order'] = $order;    
        }
    }

    $limit = std\get($kwargs, 'limit', '');
    if ($limit !== '' && $limit !== null) {// '0' is not false!
        $sql .= " limit $limit";
        if ($return)
            $return['limit'] = $limit;
    }

    if ($offset = std\get($kwargs, 'offset', '')) {
        $sql .= " offset $offset";
        if ($return)
            $return['offset'] = $offset;
    }

    return [$sql, $NewField2Type];
}

function parse_table(&$from, $Field2Type) {
    if (count($from) > 1) {
        assert (array_key_exists('join', $from) || array_key_exists('inner_join', $from));
        $using = $from['using'];
        $on = $from['on'];
        $join_type = 'join';
        [$table, $join_table] = $from['join']?? $from['inner_join'];
    }
    else if (isset($from['as']))
        return parse_expression($from, $Field2Type);
    else {
        [[$database, $table]] = std\entries($from);
        if (is_string($table)) {
            if (preg_match('/\W/', $table))
                $table = "`$table`";
            return "$database.$table";
        }

        $join_type = $database;
        [$table, $join_table] = $table;
        $using = $on = null;
    }

    if (is_array($table))
        $table = parse_table($table, $Field2Type);
    $table = "$table ".str_replace('_', ' ', $join_type)." ".parse_expression($join_table, $Field2Type);

    if ($using) {
        if (is_array($using))
            $using = implode(", ", $using);
        $table .= " using ($using)";
    }
    elseif ($on)
        $table .= " on ".parse_expression($on, $Field2Type);
    return $table;
}

function parse_expression(&$cond, &$Field2Type = null, $sep=' ', $parent=null)
{
    global $physic2logic;
    if (is_string($cond)) {
        if ($parent && array_key_exists("in", $parent))
            if ($cond != $parent['in'][0] || !isset($Field2Type[$cond]))
                return mysql\mysqlStr($cond);
        return $cond;
    }

    if (is_numeric($cond))
        return $cond;

    if (! $cond)
        return '';

    if (isset($cond['from'])) {
        [$sql] = parse_statement($cond, $Field2Type);
        if ($sep || $parent && (isset($parent['union_all']) || isset($parent['union'])) && isset($cond['limit']))
            $sql = "($sql)";
        return $sql;
    }

    if (count($cond) > 1) {
        if (std\is_list($cond))
            return implode(
                $sep,
                array_map(
                    fn (&$cond) => parse_expression(
                        $cond, 
                        $Field2Type, 
                        $sep, 
                        $parent
                    ),
                    $cond
                )
            );
        else if (array_key_exists('when', $cond) && array_key_exists('when', $cond)){
            $when = parse_expression($cond['when'], $Field2Type);
            $then = $cond['then'];
            if (is_string($then))
                $then = mysql\mysqlStr($then);
            else
                $then = parse_expression($then, $Field2Type);
            return "when $when then $then";
        }
        else 
            throw new Exception("Invalid expression: ".json_encode($cond));
    }

    [$func] = array_keys($cond);

    if (std\is_list($cond[$func])) {
        switch ($func) {
        case 'in':
        case 'not_in':
            $sep = ',';
            break;
        case 'union':
        case 'union_all':
            $sep = null;
            break;
        case 'case':
            $sep = ' ';
            break;
        case 'json_table':
            $cond[$func][1][0] = mysql\mysqlStr($cond[$func][1][0]);
            $sep = ' ';
            break;
        default:
            $sep = ' ';
        }
        $args = array_map(
            fn ($arg) => parse_expression(
                $arg, 
                $Field2Type, 
                $sep, 
                $cond
            ), 
            $cond[$func]
        );
    } else
        $args = [parse_expression(
            $cond[$func], 
            $Field2Type, 
        )];

    $funcPhysical = $func;
    $funcLogical = $physic2logic[$func] ?? $func;

    $transform = $Field2Type['__transform__'];
    switch ($funcLogical) {
    case 'and':
        // https://www.php.net/manual/en/function.usort.php
        foreach (std\enumerate($cond['and']) as [$i, $expr]) {
            if ($expr['or']?? null)
                $args[$i] = "(".$args[$i].")";
        }

        usort($args, function ($lhs, $rhs) {
            $cmp = strlen($lhs) - strlen($rhs);
            if ($cmp)
                return $cmp;

            if (preg_match('/^regexp_like|^\w+ (binary )?regexp/', $lhs) && preg_match('/^regexp_like|^\w+ (binary )?regexp/', $lhs)) {
                // chech if looking behind exists?
                if (preg_match('/\(\?<=/', $lhs)) {
                    if (preg_match('/\(\?<=/', $rhs))
                        return 0;
                    return 1;
                } else {
                    if (preg_match('/\(\?<=/', $rhs))
                        return - 1;
                    return 0;
                }
            }

            return $cmp;
        });

    case 'or':
        return implode(" $funcLogical ", array_filter($args, fn ($cond) => $cond));

    case 'as':
        $rhs = $cond[$funcPhysical][1];
        if (is_array($rhs) && ($rhs['from'] || $rhs['union'] || $rhs['union_all']))
            $args[1] = "($args[1])";

        if (std\array_any(fn (&$cond) => $cond == '' || $cond == null, $args))
            return '';

        $conds = $cond[$funcPhysical];
        if (is_string($conds[0]) && is_string($conds[1]) && !is_numeric($args[0]) && $args[0] != $Field2Type['__cte__'])
            if (! $Field2Type || ! $Field2Type[$args[0]])
                if ($Field2Type[$args[1]] != 'json' || $args[0] != 'NULL')
                        $args[0] = mysql\mysqlStr($args[0]);

        return implode(" $funcLogical ", $args);

    case 'in':
    case 'not in':
        if (is_array($cond[$funcPhysical][1])) //$cond[$funcPhysical][1]['from']
            $args[1] = "($args[1])";

        if (std\array_any(fn (&$cond) => $cond == '' || $cond == null, $args))
            return '';

        return implode(" $funcLogical ", $args);

    case 'for':
        if (std\array_any(fn (&$cond) => $cond == '' || $cond == null, $args))
            return '';

        return implode(" $funcLogical ", $args);

    case '>':
    case '<':
    case '>=':
    case '<=':
    case '+':
    case '-':
    case '*':
    case '/':
    case '%':
    case '&':
    case '^':
    case '>>':
    case '<<':
        // numeric operators:
        if (std\array_any(fn (&$cond) => $cond == '' || $cond == null, $args))
            return '';
        return implode(" $funcLogical ", $args);

    case '=':
    case '!=':
        if (std\array_any(fn (&$cond) => $cond == '' || $cond == null, $args))
            return '';

        [$lhs, &$rhs] = $args;
        if (is_string($rhs) && !is_array($cond[$func][1]) && !is_numeric($rhs) && !isset($Field2Type[$rhs])) {
            if (! $Field2Type || ! $Field2Type[$lhs] || ! mysql\is_numeric($Field2Type[$lhs])) {
                if (!mysql\is_json($Field2Type[$lhs]) || $rhs != 'NULL' || !$parent || $parent['set'] !== $cond)
                    $rhs = mysql\mysqlStr($rhs, 'regexp');
            }
        }

        return implode(" $funcLogical ", $args);

    case 'is':
    case 'is not':
        return implode(" $funcLogical ", $args);

    case 'regexp':
    case 'regexp binary':
    case 'not regexp':
    case 'not regexp binary':
        if (std\array_any(fn (&$cond) => $cond == '' || $cond == null, $args))
            return '';

        if (count($args) >= 2) {
            [$lhs, &$rhs] = $args;
            $hit = false;
            if ($transform && $transform[$lhs]) {
                $fn = "transform_$transform[$lhs]";
                if (is_callable($fn)) {
                    $rhs = $fn($rhs)[0];
                    $hit = true;
                }
            }
            if (!$hit)
                $rhs = look_behind_adjustment($rhs, false);
        }

        $conds = is_array($cond[$funcPhysical]) ? $cond[$funcPhysical] : [$cond[$funcPhysical]];
        foreach (std\enumerate(std\zipped($args, $conds)) as [$i, [$arg, $condition]]) {
            if (is_string($condition)) {
                if (! $Field2Type || !isset($Field2Type[$arg])) {
                    $args[$i] = mysql\mysqlStr($arg, 'regexp');
                }
            }
        }
        
        return implode(" $funcLogical ", $args);

    case 'like':
    case 'like binary':
    case 'not like':
    case 'not like binary':
        if (std\array_any(fn (&$cond) => $cond == '' || $cond == null, $args))
            return '';

        if (count($args) >= 2) {
            [$lhs, &$rhs] = $args;
            if ($transform && $transform[$lhs]) {
                $fn = "transform_$transform[$lhs]";
                $rhs = $fn($rhs)[0];
            }
        }

        $conds = is_array($cond[$funcPhysical]) ? $cond[$funcPhysical] : [$cond[$funcPhysical]];
        foreach (std\enumerate(std\zipped($args, $conds)) as [$i, [$arg, $condition]]) {
            if (is_string($condition)) {
                if (! $Field2Type || ! $Field2Type[$arg]) {
                    $args[$i] = mysql\mysqlStr($arg);
                }
            }
        }

        return implode(" $funcLogical ", $args);
    case '->':
    case '->>':
        if (std\array_any(fn (&$cond) => $cond == '' || $cond == null, $args))
            return '';

        if (is_string($cond[$func][1])) {
            [$lhs, &$rhs] = $args;
            $rhs = mysql\mysqlStr($rhs);
            if (is_string($cond[$func][0]))
                return implode($funcLogical, $args);
            else {
                $args = implode(', ', $args);
                return "$func($args)";    
            }
        }
        else {
            $args = implode(', ', $args);
            return "$func($args)";
        }

    case '~':
        return "~$args[0]";

    case 'path':
    case 'separator':
        $args[0] = mysql\mysqlStr($args[0]);
    case 'create':
    case 'global':
    case 'distinct':
        return "$funcLogical $args[0]";

    case 'table':
        $table = $args[0];
        $table = str_replace("'", "", $table);
        error_log('$table = ' . $table);
        $table = preg_replace('/\((\w+)\)/', '.\\1', $table);
        error_log('$table = ' . $table);
        return "$funcLogical $table";

    case 'order':
        if (count($args) == 2)
            return "order by $args[0] $args[1]";

        return "order by $args[0]";

    case 'group_concat':
    case 'count':
    case 'json_valid':
    case 'json_type':
    case 'json_arrayagg':
    case 'json_objectagg':
        return "$funcLogical($args[0])";

    case 'find_in_set':
        return "$funcLogical($args[0], $args[1])";

    case 'regexp_like':
    case 'not regexp_like':
        [$lhs, &$rhs] = $args;
        $transform_fn = $transform && $transform[$lhs];
        $rhs = look_behind_adjustment($rhs, $transform_fn);
        if ($transform_fn) {
            $fn = "transform_$transform[$lhs]";
            $rhs = $fn($rhs)[0];
        }
        
        $conds = is_array($cond[$funcPhysical]) ? $cond[$funcPhysical] : [$cond[$funcPhysical]];
        foreach (std\enumerate(std\zipped($args, $conds)) as [$i, [$arg, $condition]]) {
            if (is_string($condition)) {
                if (! $Field2Type || ! $Field2Type[$arg]) {
                    $args[$i] = mysql\mysqlStr($arg);
                }
            }
        }

    case 'if':
        [$expr, $first, $second] = $cond[$func];
        if (is_string($first))
            $args[1] = mysql\mysqlStr($first);
            
        if (is_string($second))
            $args[2] = mysql\mysqlStr($second);

    case 'json_table':
    case 'varchar':
    case 'json_length':
    case 'char_length':
    case 'length':
        $args = implode(', ', $args);
        return "$funcLogical($args)";

    case 'json_object':
        foreach (std\range(0, count($args), 2) as $i) {
            if (!$Field2Type[$args[$i]])
                $args[$i] = mysql\mysqlStr($args[$i]);
        }
        $args = implode(', ', $args);
        return "$funcLogical($args)";

    case 'union':
    case 'union all':
        return implode(" $funcLogical ", array_filter($args, fn (&$cond) => $cond));
    case 'case':
        $args = implode("\n", $args);
        return "$funcLogical $args end";

    default:
        if (is_array($cond[$funcPhysical])) {
            $conds = $cond[$funcPhysical];
            foreach (std\enumerate(std\zipped($args, $conds)) as [$i, [$arg, $condition]]) {
                if (is_string($condition) && !is_numeric($arg)) {
                    if (! $Field2Type || ! $Field2Type[$arg])
                        $args[$i] = mysql\mysqlStr($arg);
                }
            }
            $args = $conds? array_map(
                fn (&$cond) => $cond ? $cond : ($cond == 0 ? $cond : "''"),
                $args
            ): [];
            $args = implode(', ', $args);
            return "$funcLogical($args)";
        }
        elseif (is_string($cond[$funcPhysical])) {
            $table = $cond[$funcPhysical];
            if (preg_match('/\W/', $table) && $table != '*' && !(str_starts_with($table, "`") && str_ends_with($table, "`")))
                $table = "`$table`";
            return "$funcPhysical.$table";
        }
        else
            return '';
    }
}

function preprocess_kwargs(&$kwargs, &$props, &$Field2Type)
{
    $criteria = [];
    foreach ($props as $key => $value) {
        if (std\fullmatch('/transform|sample|execute|repeat|mysql|keras|torch|regex|kwargs|normalize|simplify/', $key))
            continue;

        $criteria[$key] = $value;
    }

    $cond = [];

    $extraKeys = [];
    foreach ($criteria as $key => $value) {
        if ($dtype = $Field2Type[$key]) {
            unset($props[$key]);
            if ((mysql\is_varchar($dtype) || mysql\is_json($dtype)) && ! $Field2Type['__index__'][$key])
                $cond[] = ['regexp' => [$key, $value]];
            else
                $cond[] = ['eq' => [$key, $value]];
        } else
            $extraKeys[] = $key;
    }

    if ($cond) {
        if ($kwargs['where']) {
            if ($kwargs['where']['and'])
                array_push($kwargs['where']['and'], ...$cond);
            else
                $kwargs['where'] = ['and' => [$kwargs['where'], ...$cond]];
        } else {
            if (count($cond) > 1)
                $cond = ['and' => $cond];
            else
                [$cond] = $cond;

            $kwargs['where'] = $cond;
        }
    }

    if ($extraKeys)
        $kwargs['limit'] = 0;
}
?>