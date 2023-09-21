<title>summary</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';
require_once 'init.php';

function section($axiom)
{
    [$section] = explode('.', $axiom, 2);
    return $section;
}

$repertoire = [];
$user = get_user();
foreach (select_axiom_by_state_not($user, 'proved') as $tuple) {
    [$axiom, $state] = $tuple;
    $repertoire[section($axiom)][$state][] = $axiom;
}

$state_count_pairs = [];

foreach (get_rows("select state, count(*) as count from axiom where user = '$user' group by state order by count", MYSQLI_ASSOC) as $res) {
    $state_count_pairs[] = $res;
}

$state_count_pairs[] = [
    'state' => 'total',
    'count' => select_count($user)
];
?>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

<script src="static/unpkg.com/vue@3.2.47/dist/vue.global.prod.js"></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>
<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>

<script type=module>    
createApp('axiomSummary', {
		state_count_pairs : <?php echo std\encode($state_count_pairs)?>,
		repertoire : <?php echo std\encode($repertoire)?>,
});

</script>
