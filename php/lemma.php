<?php
// ^ *error_log
require_once 'init.php';
require_once 'std.php';
if ($_POST) {
	$term = "(?:[A-Z][\w']*|(of|eq|ne|gt|lt|ge|le|is|in|to|mod|et|ou)(?=\.)|comm\b)";
	$sections = std\listdir($root = dirname(dirname(__FILE__)) . "/Axiom/");
	$sectionRegex = implode('|', $sections);

	$leanCode = [];

	$imports = std\decode($_POST['imports']);
	if (is_string($imports))
		$imports = [$imports];
	$moduleExists = [];

	$open = std\decode($_POST['open']);
	$open_section = [];
	$open_mathlib = [];
	$open_variable = [];
	if ($open) {
		foreach ($open as $packages) {
			if (std\is_list($packages)) {
				foreach ($packages as $package) {
					if (in_array($package, $sections))
						$open_section[] = $package;
					else
						$open_mathlib[] = $package;
				}
			} else
				$open_variable[] = $packages;
		}
	}

	$def = $_POST['def'];
	if (is_string($def))
		$def = std\decode($def);
	if ($def)
		$def = "\n\n" . implode("\n\n\n", $def);

	$lemmaCode = [];
	foreach ($_POST['lemma'] as $lemma) {
		if ($comment = $lemma['comment'] ?? '')
			$comment = "/--\n$comment\n-/\n";

		if ($attribute = $lemma['attribute'] ?? null) {
			$attribute = std\decode($attribute);
			$attribute = '@[' . implode(", ", $attribute) . "]\n";
		} else
			$attribute = "";

		if ($accessibility = $lemma["accessibility"] ?? null)
			$accessibility = "$accessibility ";
		else
			$accessibility = "";

		$name = $lemma["name"];
		$declspec = [];
		$instImplicit = $lemma["instImplicit"] ?? '';
		if ($instImplicit)
			$declspec[] = preg_replace("/^/m", '  ', $instImplicit);

		$implicit = $lemma["implicit"] ?? '';
		if ($implicit)
			$declspec[] = preg_replace("/^/m", '  ', $implicit);

		$given = $lemma["given"] ?? '';
		if ($given) {
			$declspec[] = "-- given";
			$given = array_map(fn($line) => preg_replace("/^/m", '  ', $line), $given);
			array_push($declspec, ...$given);
		}

		$explicit = $lemma["explicit"] ?? '';
		if ($explicit) {
			if (!$given)
				$declspec[] = "-- given";
			$declspec[] = preg_replace("/^/m", '  ', $explicit);
		}

		$declspec = implode("\n", $declspec);

		$imply = preg_replace("/^/m", '  ', $lemma["imply"]);

		$proof = $lemma['proof'];
		$by = $proof['by'] ? 'by' : ($proof['calc'] ? 'calc' : '');
		if ($by)
			$proof = $proof[$by];

		foreach ($proof as &$line) {
			while (preg_match("/\b($sectionRegex)((?:\.$term)+)/", $line, $matches)) {
				if (!in_array($matches[1], $open_section))
					$open_section[] = $matches[1];

				$module = "Axiom." . $matches[0];
				if (!in_array($module, $imports))
					$imports[] = $module;

				$line = preg_replace("/\b($sectionRegex)\.(?=$term)/", '', $line);
			}

			if ($matches = std\matchAll("/\b(?!(?:$sectionRegex)\b)($term(?:\.$term)*)/", $line)) {
				foreach ($matches as [[$submodule]]) {
					foreach ($sections as $section) {
						$module = $section . '.' . $submodule;

						if (file_exists(module_to_lean($module))) {
							$module = 'Axiom.' . $module;
							if (!in_array($module, $imports))
								$imports[] = $module;
							$moduleExists[$module] = true;
							if (!in_array($section, $open_section))
								$open_section[] = $section;
							break;
						}
					}
				}
			}
		}
		$proof = array_map(fn($line) => preg_replace("/^/m", '  ', $line), $proof);
		$proof = ltrim(implode("\n", $proof), "\n");
		$proof = rtrim($proof);
		$proof = preg_replace("/(?<=\n)\s+\n/", '', $proof);
		if ($declspec)
			$declspec = "\n$declspec";
		if (!str_ends_with($declspec, ':')) 
			$declspec .= " :";
		$proof = <<<EOT
$comment$attribute{$accessibility}lemma $name$declspec
-- imply
$imply
-- proof
$proof
EOT;
		$lemmaCode[] = $proof;
	}
	$lemmaCode = implode("\n\n\n", $lemmaCode);
	$imports = array_filter($imports, function ($import) use ($lemmaCode, $open_section) {
		$imports = explode('.', $import);
		switch ($imports[0]) {
		case 'Axiom':
			array_shift($imports);
			if (in_array($imports[0], $open_section))
				array_shift($imports);
			$import = implode('.', $imports);
			break;
		case 'sympy':
		case 'stdlib':
		case 'Mathlib':
			return true;
		}
		$import = str_replace('.', '\.', $import);
		return preg_match("/\b$import\b/", $lemmaCode);
	});
	if (!array_filter($imports, fn($import) => str_starts_with($import, 'Axiom.')))
		$imports[] = "Axiom.Basic";

	$open_section = array_reduce($imports, function ($carry, $import) use (&$moduleExists) {
		$module = explode('.', $import);
		if ($module[0] == 'Axiom' && $module[1] != 'Basic')
			$carry[$module[1]] = true;
		return $carry;
	}, []);
	$imports = array_map(fn($import) => "import $import", $imports);
	// find Axiom -name "*.lean" -exec perl -i -0777 -pe 's/(\S+)(?=\n\n@\[\w+)/$1\n/g' {} +
	// find Axiom -name "*.lean" -exec perl -i -0777 -pe 's/((\S+)\n+)(?=\n\n\n-- created)/$2/g' {} +
	$leanCode[] = implode("\n", $imports);

	$open_section = array_keys($open_section);
	$open_section = array_merge($open_section, $open_mathlib);
	if ($open_section)
		$leanCode[] = "open " . implode(" ", $open_section);
	foreach ($open_variable as $entity) {
		[[$section, $variables]] = std\entries($entity);
		$variables = implode(" ", $variables);
		$leanCode[] = "open $section ($variables)";
	}

	if ($def)
		$leanCode[] = $def;

	$leanCode[] = "\n\n" . $lemmaCode;

	$date = std\decode($_POST['date']);
	$created = $date['created'];

	$leanCode[] = "\n\n-- created on $created";

	$updated = date('Y-m-d');
	if ($updated != $created)
		$leanCode[] = "-- updated on $updated";

	$leanCode[] = "";

	$leanCode = array_map(fn($line) => str_replace("\r", '', $line), $leanCode);
	$file = new std\Text($leanFile);
	$file->writelines($leanCode);
}

$code = null;
$leanEchoFile = preg_replace('/\.lean$/', '.echo.lean', $leanFile);

if (!file_exists($leanEchoFile) || filemtime($leanFile) < filemtime($leanEchoFile)) {
	$code = fetch_from_mysql(get_project_name(), $module);
	if ($code) {
		$code['imports'] = std\decode($code['imports']);
		$code['open'] = std\decode($code['open']);
		$code['def'] = std\decode($code['def']);
		$code['lemma'] = std\decode($code['lemma']);
		$code['error'] = std\decode($code['error']);
		$code['date'] = std\decode($code['date']);
		if (!file_exists($leanEchoFile))
			std\createNewFile($leanEchoFile);
	}
}

if (!$code || !$code['lemma'] || !$code['date']) {
	// $_ = new std\Timer("compile and render2vue");
	$leanCode = compile(file_get_contents($leanFile));
	$syntax = [];
	$code = $leanCode->render2vue(false, $modify, $syntax);
	$import_syntax = function ($import) use ($leanCode, $code) {
		if (!in_array($import, $imports = $code['imports'])) {
			$prefix = "Axiom.";
			$imports = array_filter($imports, fn($module) => str_starts_with($module, $prefix));
			$imports = [...$imports];
			$offset = strlen($prefix);
			$imports = array_map(fn($module) => substr($module, $offset), $imports);
			$imports = std\encode($imports);
			$imports = mysql\mysqlStr($imports);
			$sql = <<<EOF
WITH RECURSIVE dependencies AS (
	select 
		* 
	from 
		json_table(
			$imports,
			'$[*]' columns(module text path '$')
		) as jt
	UNION ALL
	SELECT
		SUBSTRING(jt.module, LOCATE('.', jt.module) + 1)
	FROM
		dependencies
		JOIN axiom.lemma as _t using(module)
		CROSS JOIN JSON_TABLE(
			_t.imports,
			'$[*]' COLUMNS (module text PATH '$')
		) AS jt
	WHERE
		jt.module LIKE 'Axiom.%'
)
select 
    count(*)
from dependencies 
    JOIN axiom.lemma as _t using(module)
    cross join json_table(
        imports,
        '$[*]' columns(module text path '$')
    ) as jt
where 
	jt.module = "$import"
EOF;
			[[$count]] = get_rows($sql, MYSQLI_NUM);
			if (!intval($count)) {
				array_unshift($code['imports'], $import);
				$leanCode->import($import);
				return true;
			}
		}
		return false;
	};

	foreach ($syntax as $tac => $_) {
		switch ($tac) {
		case 'denote':
			$modify |= $import_syntax('sympy.core.relational');
			break;
		case 'mp':
		case 'mpr':
			$modify |= $import_syntax('sympy.core.logic');
			break;
		case '²':
		case '³':
		case '⁴':
			$modify |= $import_syntax('sympy.core.power');
			break;
		case 'Ici':
		case 'Iic':
		case 'Ioi':
		case 'Iio':
		case 'Ioc':
		case 'Ioo':
		case 'Icc':
		case 'Ico':
		case 'range':
			$modify |= $import_syntax('sympy.sets.sets');
			break;
		case 'setOf':
			$modify |= $import_syntax('sympy.concrete.quantifier');
			break;
		case 'LLamda':
			$modify |= $import_syntax('sympy.concrete.expr_with_limits.lamda');
			break;
		case 'Tensor':
		case 'Ones':
		case 'Zeros':
			$modify |= $import_syntax('sympy.tensor.tensor');
			break;
		}
	}
	if ($modify) {
		$file = new std\Text($leanFile);
		$file->write("$leanCode");
	}
}
?>

<title><?php echo $title; ?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<link rel=stylesheet href="static/unpkg.com/katex@0.16.21/dist/katex.min.css">
<link rel=stylesheet href="static/unpkg.com/prismjs@1.30.0/themes/prism.min.css" />
<body></body>
<?php
include_once 'script.php';
?>
<script src="static/unpkg.com/lz-string@1.5.0/libs/lz-string.js"></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/katex.min.js"></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/contrib/auto-render.min.js"></script>
<script src="static/unpkg.com/prismjs@1.30.0/prism.js"></script>
<script src="static/unpkg.com/prismjs@1.30.0/components/prism-lean.js"></script>
<script type=module>
import * as codemirror from "./static/codemirror/lib/codemirror.js"
import * as lean from "./static/codemirror/mode/lean/lean.js"
import * as active_line from "./static/codemirror/addon/selection/active-line.js"
import * as show_hint from "./static/codemirror/addon/hint/show-hint.js"
import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js"
import * as comment from "./static/codemirror/addon/comment/comment.js"

createApp('render', <?php echo std\encode($code) ?>);

//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>