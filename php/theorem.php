<?php
// ^ *error_log
require_once 'init.php';

$import = $code['import'];
$open = $code['open'];
$namespace = $code['namespace'];
$theorem = $namespace['theorem'];
$date = $code['date'];
$error = $code['error'];
$proof = $theorem['proof'];
$imply = $theorem['imply'];

if (isset($proof['by'])) {
    $proof = $proof['by'];
    $imply .= " := by";
}
else
    $imply .= " :=";

$latex = [
    'given' => $theorem['given'],
    'imply' => $imply,
    'proof' => array_map(fn ($arg) => '', $proof)
];
?>

<title><?php echo $title;?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<style>
div {
	caret-color: transparent;
}
</style>
<body></body>
<script src="static/unpkg.com/vue@3.2.47/dist/vue.global.prod.js"></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

<script src='static/js/std.js'></script>
<script src='static/js/utility.js'></script>
<script>
MathJax = InitMathJax(1000);
</script>
<script async src="static/unpkg.com/mathjax@3.2.0/es5/tex-chtml.js"></script>

<script type=module>
import * as codemirror from "./static/codemirror/lib/codemirror.js"
import * as python from "./static/codemirror/mode/python/python.js"
import * as active_line from "./static/codemirror/addon/selection/active-line.js"
import * as show_hint from "./static/codemirror/addon/hint/show-hint.js"
import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js"

createApp('render', {
    module: <?php echo std\encode($module)?>,
    imports: <?php echo std\encode($import)?>,
    open: <?php echo std\encode($open)?>,
    namespace : <?php echo std\encode($namespace)?>,
    error : <?php echo std\encode($error)?>,
    date: <?php echo std\encode($date)?>,
    latex: <?php echo std\encode($latex)?>,
});

//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>


