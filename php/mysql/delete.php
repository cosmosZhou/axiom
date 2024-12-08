<?php
require dirname(__file__).'/../regexp/SyntaxMatcher.php';
require dirname(__file__).'/../xml/RichText.php';

if (! $kwargs['limit'])
    $kwargs['limit'] = '40';

$kwargs['select'] = '*';
$Field2Type = ['__props__' => $props];
[$sql_select, $Field2Type] = parse_statement($kwargs, $Field2Type);

unset($kwargs['select']);

load_data($sql_select, $Field2Type);

$kwargs['delete'] = true;
if (!$sql)
    [$sql] = parse_statement($kwargs, $Field2Type);

?>