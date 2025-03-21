<?php
// ^ *error_log
require_once 'init.php';
require_once 'std.php';
if ($_POST) {
	$sections = ['Algebra', 'Calculus', 'Discrete', 'Geometry', 'Neuro', 'Set', 'Probability'];
	$sectionRegex = implode('|', $sections);

	$leanCode = [];

	$imports = std\decode($_POST['imports']);
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

	$def = std\decode($_POST['def']);
	if ($def) {
		$def = array_map(fn($def) => "$def", $def);
		$def = implode("\n", $def);
	}

	$lemmaCode = [];
	foreach ($_POST['lemma'] as $lemma) {
		if ($comment = $lemma['comment'] ?? '')
			$comment .= "\n";

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
		if ($explicit)
			$declspec[] = preg_replace("/^/m", '  ', $explicit);

		$declspec = implode("\n", $declspec);

		$imply = preg_replace("/^/m", '  ', $lemma["imply"]);

		$proof = $lemma['proof'];
		$by = $proof['by'] ? 'by' : ($proof['calc'] ? 'calc' : '');
		if ($by)
			$proof = $proof[$by];

		foreach ($proof as &$line) {
			while (preg_match("/\b($sectionRegex)((?:\.\w+)+)/", $line, $matches)) {
				if (!in_array($matches[1], $open_section))
					$open_section[] = $matches[1];

				$module = "Axiom." . $matches[0];
				if (!in_array($module, $imports))
					$imports[] = $module;

				$line = preg_replace("/\b($sectionRegex)\.(?=\w+)/", '', $line);
			}

			if ($matches = std\matchAll("/\b(?!(?:$sectionRegex)\b)(\w+(?:\.\w+)+)/", $line)) {
				foreach ($matches as [[$submodule]]) {
					foreach ($open_section as $section) {
						$module = $section . '.' . $submodule;
						$moduleFile = module_to_lean($module);
						if (file_exists($moduleFile)) {
							$module = 'Axiom.' . $module;
							if (!in_array($module, $imports))
								$imports[] = $module;
							$moduleExists[$module] = true;
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
		else
			$declspec = ":";
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
	if (count($imports) > 1 && in_array('Axiom.Basic', $imports))
		std\array_delete($imports, array_search('Axiom.Basic', $imports));

	$imports = array_filter($imports, function ($import) use ($lemmaCode, $open_section) {
		$imports = explode('.', $import);
		if ($imports[0] == 'Axiom') {
			array_shift($imports);
			if (in_array($imports[0], $open_section))
				array_shift($imports);
			$import = implode('.', $imports);
		}
		$import = str_replace('.', '\.', $import);
		return preg_match("/\b$import\b/", $lemmaCode);
	});
	if (!$imports)
		$imports[] = "Axiom.Basic";
	$imports = array_map(fn($import) => "import $import", $imports);
	// find Axiom -name "*.lean" -exec perl -i -0777 -pe 's/(\S+)(?=\n\n@\[\w+)/$1\n/g' {} +
	// find Axiom -name "*.lean" -exec perl -i -0777 -pe 's/((\S+)\n+)(?=\n\n\n-- created)/$2/g' {} +
	$leanCode[] = implode("\n", $imports);

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
	$code = compile(file_get_contents($leanFile))->render2vue(false);
}
?>

<title><?php echo $title; ?></title>
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

createApp('render', <?php echo std\encode($code) ?>);

//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>