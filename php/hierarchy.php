<title>hierarchy</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';
require_once 'init.php';

// ^ *error_log

$array_keys = array_keys($_GET);

if (count($array_keys) > 1) {
    // print_r($_GET);
    $deep = json_decode($_GET['deep']);
    unset($_GET['deep']);
} else {
    $deep = false;
}

$keyInput = array_keys($_GET)[0];

switch ($keyInput) {
    case 'callee':
        $key = 'caller';
        $invert = true;
        break;

    case 'caller':
        $key = 'callee';
        $invert = false;
        break;
}

$module = $_GET[$keyInput];
$module = str_replace('/', '.', $module);

$user = get_project_name();
$graph = establish_hierarchy($user, $module, $invert);

$graph->detect_cycle_traceback($module, $parent);

if ($parent) {
    $cyclicProof = $parent[0];

    for ($i = 1; $i < count($parent); ++ $i) {
        if ($parent[$i] == $cyclicProof)
            break;
    }

    $parent[] = $module;
    
    $traceback = [];
    for ($j = count($parent) - 1; $j >= $i; -- $j)
        $traceback[] = $parent[$j];
} else
    $traceback = null;

include_once 'script.php';
?>

<script type=module>
createApp('hierarchy', {
	module : <?php echo std\encode($module)?>,
	graph : <?php echo std\encode($graph)?>,
	traceback: <?php echo std\encode($traceback)?>,
	keyInput : <?php echo std\encode($keyInput)?>,
    deep: <?php echo std\encode($deep)?>,
});

</script>

