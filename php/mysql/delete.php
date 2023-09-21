<?php
require dirname(__file__).'/../regexp/SyntaxMatcher.php';
require dirname(__file__).'/../xml/RichText.php';

if (! $kwargs['limit']) {
    $kwargs['limit'] = '40';
}

[$Field2Type, $primary_key, $indexKey] = mysql\field_to_type($database, $table);

preprocess_kwargs($kwargs, $props, $Field2Type, $indexKey);

$kwargs['select'] = '*';
[$sql_select, $table] = parse_statement($kwargs, $Field2Type, $transform);

unset($kwargs['select']);

load_data($sql_select, $Field2Type);

$kwargs['delete'] = true;
if (!$sql) {
    [$sql, $table] = parse_statement($kwargs, $Field2Type, $transform);
}

?>