<!DOCTYPE html>
<meta charset="UTF-8">
<?php
require_once 'utility.php';

$module = $_GET['new'];

$module = str_replace("/", ".", $module);

$code = fetch_codes($module);
if (!$code) {
    require_once 'init.php';
    $sql = <<<EOT
select 
    *
from 
    mathlib 
where 
    name = "$module"
EOT;
    [$lemma] = get_rows($sql);
    if ($lemma) {
        $lemma['imply'] = std\decode($lemma['imply']);
        $lemma['imply']['lean'] .= " :=";
        $lemma['imply']['latex'] .= "\\tag*{ :=}";
        $proof = $module;
        $vars = [];
        if ($explicit = $lemma['default'] ?? null) {
            unset($lemma['default']);
            $parser = compile($explicit);
            array_push($vars, ...$parser->parse_vars_default($parser->args));
            $explicit .= " :";
            $lemma['explicit'] = $explicit;
        }
    
        if ($given = $lemma['given'] ?? null) {
            $given = std\decode($given);
            foreach ($given as $g) {
                $parser = compile($g['lean']);
                array_push($vars, ...$parser->parse_vars_default($parser->args));
            }
            if (!$explicit)
                $given[count($given) - 1]['lean'] .= " :";
            $lemma['given'] = $given;
        }
        $proof .= implode("", array_map(fn($args) => " $args[0]", $vars));
        $lemma['proof'] = [
            [
                'lean' => $proof
            ]
        ];
    }
    else {
        $sql = <<<EOT
select 
    *
from 
    axiom
where 
    axiom = "$module"
EOT;
        [$lemma] = get_rows($sql);
        $latex = $lemma['latex'];
        $latex = explode("\n", $latex);
        $lean = $lemma['lean'];
        $lean = std\decode($lean);
        $lemma['imply'] = [
            'lean' => $lean[0],
            'latex' => preg_replace("/\\\\tag\*\{.*\}$/", "", std\substring($latex[0], 2, -2))
        ];
        $lemma['imply']['lean'] .= " := by";
        $lemma['imply']['latex'] .= "\\tag*{ := by}";
        $proof = 'sorry';
        $lemma['proof'] = [
            'by' => [
                [
                    'lean' => $proof
                ]
            ]
        ];
    }
    $lemma['name'] = 'main';
    $lemma['accessibility'] = 'private';
    $lemma['attribute'] = ['main'];
    
    $code = [
        'module' => $module,
        'imports' => [],
        'open' => [],
        'def' => [], 
        'lemma' => [$lemma],
        'error' => [],
        'date' => [
            'created' => date('Y-m-d')
        ],
    ];
}
?>

<title><?php echo $module;?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<link rel=stylesheet href="static/unpkg.com/katex@0.16.21/dist/katex.min.css">
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

createApp('newTheorem', <?php echo std\encode($code) ?>);

</script>