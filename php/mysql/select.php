<?php

require dirname(__file__).'/../regexp/SyntaxMatcher.php';
require dirname(__file__).'/../xml/RichText.php';

$download = std\pop($props, 'download');

if (!$is_union) {
    if (std\not($kwargs['limit']))
        $kwargs['limit'] = '40';
}

$Field2Type = ['__props__' => $props];
[$sql, $Field2Type] = parse_statement($kwargs, $Field2Type);

$scanCriteria = search_for_scan_criteria($kwargs, $Field2Type);

if ($scanCriteria && count($scanCriteria) > 1)
    scan_data($sql, $Field2Type, $kwargs);
else
    load_data($sql, $Field2Type, $table && ($kwargs['select'] == '*' || $kwargs['select'] == ['*']));

if ($download) {
    function fetch_data($table, &$data, $target = null, $batch_size = null, $offset = 0, $primary_key = '')
    {
        $id = std\uuid();
        if ($batch_size) {
            $offset = $offset ? (int)$offset : 0;

            $root = $id;
            std\createDirectory($root);
            error_log("generating root folder: $root");

            $start = $offset;

            foreach (std\batches($data, $batch_size) as &$data) {
                $stop = $start + count($data);
                
                if (count($data) == 1 && $primary_key) {
                    $unique_key = $data[0][$primary_key];
                    $filename = "$root/$unique_key.json";
                }
                else
                    $filename = "$root/$start-$stop.json";

                fetch_data($table, $data, $filename);
                $start = $stop;
            }
            
            $target = "$table-$id.zip";
            
            error_log("generating zip file: $target");
            std\makezip($root, $target);
        } else {
            if (! $target)
                $target = "$table-$id.json";
            elseif (!std\contains($target, ".")) {
                if ($target == 'jsonl')
                    $jsonl = true;
                $target = "$table-$id.$target";
            }
                
            std\createNewFile($target);
            $file = new std\Text($target);
            if ($jsonl)
                $file->writelines(array_map(fn(&$obj) => std\encode($obj), $data));
            else
                $file->write(std\encode($data));
        }
        
        return $target;
    }
    
    $batch_size = std\pop($props, 'batch_size');
    $batch_size = (int)$batch_size;
    switch ($download) {
    case 'json':
    case 'jsonl':
    case 'zip':
        $ext = $download;
        break;
    default:
        $ext = $batch_size? 'zip': 'json';
        break;
    }

    $filename = fetch_data($table, $data, $ext, $batch_size, $offset, (! $select || $select == '*') && $batch_size == 1 ? $Field2Type['__primary_key__'] : '');
    std\send_from_directory(dirname($filename), basename($filename), true);
    unlink($filename);
    die(0);
}

if ($is_union || $kwargs['select'] && $kwargs['select'] != '*' && $kwargs['select'] != ['*'])
    $dual = true;
elseif (isset($kwargs['with']) || isset($kwargs['with_recursive']))
    $dual = !is_string($database) || !is_string($table);
else
    $dual = false;
?>