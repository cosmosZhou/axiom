<?php
require_once '../../utility.php';
require_once '../../mysql.php';
use std\Text;

$dict = empty($_POST) ? $_GET : $_POST;

$data = $dict['data'];

error_log("data = " . $data);
$data = json_decode($data);

$ROOT = $_SERVER['DOCUMENT_ROOT'];

list ($user, $axiom, $state, $lapse, $latex) = $data;

// $latex = str_replace('"', '\\"', $latex);
// $latex = str_replace("\\'", "'", $latex);


$latex = json_encode($latex, JSON_UNESCAPED_UNICODE);

error_log("latex = $latex");
$query = "update tbl_axiom_py set state = \"$state\", lapse = $lapse, latex = $latex where user = \"$user\" and axiom = \"$axiom\"";

$affected_rows = \mysql\execute($query);
if ($affected_rows < 1) {
    $query = "insert into tbl_axiom_py values(\"$user\", \"$axiom\", \"$state\", $lapse, $latex)";
    error_log("query = $query");
    $affected_rows = \mysql\execute($query);
}

// error_log("axiom = $axiom");
$tuples = [];

$tokens = explode('.', $axiom);
$tokens[] = "apply";

$prefix = "";

$size = count($tokens) - 1;
for ($i = 0; $i < $size; ++ $i) {
    $prefix .= $tokens[$i] . ".";
    $phrase = $tokens[$i + 1];
    $usage = 1;

    $tuples[] = [
        $user,
        $prefix,
        $phrase,
        $usage
    ];
}

// error_log(\std\jsonify($tuples));
\mysql\insertmany("tbl_suggest_py", $tuples);

$theorem = str_replace('.', '/', $axiom);
$dir = $ROOT . "/" . $user . "/axiom";
$py = "$dir/$theorem.py";
if (! file_exists($py)) {
    $py = "$dir/$theorem/__init__.py";
}

// error_log("py = $py");
$linkCount = [];
foreach (yield_from_py($py) as $dict) {
    if (array_key_exists('a', $dict)) {
        $a = $dict['a'];
        foreach ($a as $line => $link) {
            if (! array_key_exists($link, $linkCount)) {
                $linkCount[$link] = 0;
            }
            ++ $linkCount[$link];
        }
    }
}

// error_log("linkCount = " . \std\jsonify($linkCount));

$tuples = [];
$caller = $axiom;
foreach ($linkCount as $callee => $count) {
    $tuples[] = [
        $user,
        $caller,
        $callee,
        $count
    ];
}

\mysql\execute("delete from tbl_hierarchy_py where user = '$user' and caller = '$caller'");

if ($tuples)
    \mysql\insertmany("tbl_hierarchy_py", $tuples, false);

?>