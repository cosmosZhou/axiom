<?php
require_once 'std.php';
require_once 'mysql.php';
require_once 'init.php';

$name = $_GET["mathlib"];
$mathlib = [
    'name' => $name
];
foreach (get_rows("select * from mathlib where name = \"$name\"", MYSQLI_NUM) as [$name, $type, $instImplicit, $strictImplicit, $implicit, $given, $explicit, $imply]) {
    $mathlib = array_merge($mathlib, [
        'type' => $type,
        'instImplicit' => $instImplicit,
        'strictImplicit' => $strictImplicit,
        'implicit' => $implicit,
        'given' => std\decode($given),
        'explicit' => $explicit,
        'imply' => std\decode($imply)
    ]);
}
?>

<title><?php echo $name;?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<link rel=stylesheet href="static/unpkg.com/katex@0.16.21/dist/katex.min.css">
<body></body>
<?php
include_once 'script.php';
?>
<script defer src="static/unpkg.com/katex@0.16.21/dist/katex.min.js"></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/contrib/auto-render.min.js"></script>
<script type=module>
import * as codemirror from "./static/codemirror/lib/codemirror.js"
import * as lean from "./static/codemirror/mode/lean/lean.js"
import * as active_line from "./static/codemirror/addon/selection/active-line.js"
import * as show_hint from "./static/codemirror/addon/hint/show-hint.js"
import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js"
import * as comment from "./static/codemirror/addon/comment/comment.js"

createApp('mathlib', <?php echo std\encode($mathlib)?>);
</script>
