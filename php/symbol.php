<?php
require_once 'std.php';
require_once 'mysql.php';
require_once 'init.php';

$symbol = $_GET["symbol"];

foreach (get_rows("select script, latex from symbol where symbol = '$symbol'", MYSQLI_NUM) as [$script, $latex]) {
    error_log("script = " . std\encode($script));
    error_log("latex = " . std\encode($latex));
    $latex = trim($latex);
    $latex = json_decode($latex, true);

    $script = json_decode($script);

    for ($i = 0; $i < count($latex); ++ $i) {
        $statements[] = [
            'script' => $script[$i],
            'latex' => $latex[$i]
        ];
    }
}

$statements[] = [
    'script' => '',
    'latex' => ''
];
?>

<title><?php echo $symbol;?></title>
<body></body>
<script src="static/unpkg.com/vue@3.2.47/dist/vue.global.prod.js"></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>
<script>
MathJax = InitMathJax(300);
</script>
<script async src="static/unpkg.com/mathjax@3.2.0/es5/tex-svg.js"></script>

<script type=module>
createApp('console', {
    statements : <?php echo std\encode($statements)?>,
});
</script>
