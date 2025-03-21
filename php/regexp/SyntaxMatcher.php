<?php
require_once __DIR__.'/Lexeme.php';
require_once __DIR__.'/wordClass.php';
require_once __DIR__.'/balancedMatch.php';

$braceAsDelimiter = "(?:(?<!\\[\\^)(?<!\\[\\^[{}])[{}])+[*+?]?";
//ignore [^{}]*, [^{}]?, [^{}]+, [^}{]*, [^}{]?, [^}{]+

$braceInBrackets = "\\[[{}]+\\][*+?]?";
$nonbraceInBrackets = "\\[\\^[{}]+\\][*+?]?";

// a legal left parenthesis is represented by
$leftParenthesis = "\((?!(?:\?:)?(?:[{}|]|$braceInBrackets)+\))";

// a legal left bracket is represented by
$leftBracket = "(?<=[\\\\])\\[|\\[(?![{}])";

// a legal $right bracket is represented by
$rightBracket = "(?<![{}])\\]|(?<=[\\\\])\\]";

$legalBracket = "$leftBracket|$rightBracket";

global $outsidePairedBrackets, $insidePairedBrackets;

$dotsOutsidePairedBrackets = "(?<![\\\\])\.+[*+?]?$outsidePairedBrackets";

$dotInsidePairedBrackets = "\.$insidePairedBrackets";

$braceOutsidePairedBrackets = "([{}])$outsidePairedBrackets";

$erroneousBrackets = "\((?:\?:)?(?:[{}|]|$braceInBrackets)+\)";

$bracketsToCapture = "[{}][*+?]|$braceInBrackets|$erroneousBrackets";

$regexToSegment = "/$dotsOutsidePairedBrackets|(?:$nonbraceInBrackets|[\\\\][.]|[^{}.\\[\\](]|$dotInsidePairedBrackets|$legalBracket|$leftParenthesis)+|($bracketsToCapture)/";

function split2array($x, $y, $endlingSpaces)
{
    if ($endlingSpaces == null)
        $endlingSpaces = true;
    // error_log("x = ".$x);
    // error_log("y = ".$y);

    if ($endlingSpaces) {
        $x = preg_replace("\\((?!\\?)", "(?:", $x);
        $y = preg_replace("\\((?!\\?)", "(?:", $y);

        if (str_ends_with($x, " +") || str_ends_with($x, "\\s")) {
            $x .= "\\S?";
            $y .= "\\S?";
        }
    }

    $x_arr = split("/\\s\\+|\\s+/", $x);
    $y_arr = split("/\\s\\+|\\s+/", $y);

    return [$x_arr,$y_arr];
}

class TextMatcher
{

    public function __get($vname)
    {
        switch ($vname) {
            case 'regexp':
                return $this->text;
            default:
                return null;
        }
    }

    static public function construct($x_arr, $y_arr)
    {
        $i = 0;
        $j = 0;
        $ii = 0;
        $jj = 0;

        $e = [];

        while ($i < count($x_arr)) {
            $_x = std\substring($x_arr[$i], $ii);
            $_y = std\substring($y_arr[$j], $jj);
            if ($_x . startsWith($_y)) {
                $e . push($_y);
                $ii += strlen($y_arr[$j]) - $jj;
                if ($ii == strlen($x_arr[$i])) {
                    $i += 1;
                    $ii = 0;
                }
                $j += 1;
                $jj = 0;
            } else {
                assert($_y . startsWith($_x));
                $e . push($_x);

                $jj += strlen($x_arr[$i]) - $ii;
                if ($jj == strlen($y_arr[$j])) {
                    $j += 1;
                    $jj = 0;
                }
                $i += 1;
                $ii = 0;
            }
        }

        assert($j == strlen($y_arr));

        assert($e . join("") == $x_arr . join(""));
        assert($e . join("") == $y_arr . join(""));

        // error_log("e = " + $e);

        $j = 0;
        for ($i = 0; $i < strlen($x_arr); ++ $i) {
            $s = "";
            while ($x_arr[$i]) {
                $s .= '(' . std\substring($x_arr[$i], 0, strlen($e[$j])) . ')';
                $x_arr[$i] = std\substring($x_arr[$i], strlen($e[$j]));
                $j += 1;
            }
            $x_arr[$i] = $s;
        }
        $j = 0;
        for ($i = 0; $i < strlen($y_arr); ++ $i) {
            $s = "";
            while ($y_arr[$i]) {
                $s .= "$" . ($j + 1);
                $y_arr[$i] = std\substring($y_arr[$i], strlen($e[$j]));
                $j += 1;
            }
            $y_arr[$i] = $s;
        }

        $text = $x_arr . join(" +");
        $text_replacement = $y_arr . join(" ");
        return [$text,$text_replacement];
    }

    function __construct(...$arguments)
    {
        if (! count($arguments))
            return;

        [$_x,$_y] = $arguments;
        $xy = split2array($_x, $_y);

        $x_arr = $xy[0];
        $y_arr = $xy[1];

        if ($x_arr . join("") != $y_arr . join("")) {
            $this->text = $_x;
            $this->text_replacement = $_y;
            return;
        }

        $arr = construct($x_arr, $y_arr);
        $this->text = $arr[0];
        $this->text_replacement = $arr[1];
    }
}

class SyntaxFilterExpression
{

    public function __construct($regulation, $projective = true, $scan=false)
    {
        $this->projective = $projective;
        if ($scan) {
            $this->regulation = $regulation;
            $this->backwardSubstitution = null;
        }
        else {
            [$this->backwardSubstitution,$this->regulation] = remove_capture_unnamed($regulation);
        }
        
        [$this->regulation,$this->indexMapping] = $this->segment($this->regulation);
        $this->regulation = preg_replace_callback("/(?<=[\\\\])\\d+/", fn (&$m) => $this->indexMapping[$m[0][0]], $this->regulation);

        $this->braceIsPrefixed = false;
        $this->beginIsConsumed = false;
    }

    function construct_regex($regulation)
    {
        $start = 0;
        $regexp = [];
        global $braceAsDelimiter, $braceOutsidePairedBrackets, $braceInBrackets, $erroneousBrackets;
        foreach (std\matchAll("/($braceAsDelimiter)|($braceInBrackets)|($erroneousBrackets)/", $regulation) as [&$m, $index]) {
            $mText = $m[0];
            if ($index > $start)
                $regexp[] = $this->process(std\substring($regulation, $start, $index));

            if ($m[1]) {
                $regexp[] = preg_replace("/([{}])/", '\\\\$1', $m[1]);
                $this->update_status($m);
            } elseif ($m[2]) {
                $regexp[] = $m[2];
                $this->update_status($m);
            } else {
                $s = preg_replace("/$braceOutsidePairedBrackets/", '\\\\$1', $m[3]);
                $regexp[] = $s;
                if (!Regex::compile($s)->is_possibly_empty()) {
                    $this->braceIsPrefixed = true;
                    $this->beginIsConsumed = true;
                }
            }

            $start = $index + strlen($mText);
        }

        if (strlen($regulation) > $start) {
            $regexp[] = $this->process(std\substring($regulation, $start));
            if (!$this->braceIsPrefixed)
                $regexp[] = '(?=[{}]|$)';
        }

        return implode('', $regexp);
    }

    function update_status(&$m)
    {
        if (preg_match("/([+])|([*?])/", $m[0], $matches)) {
            if ($matches[2])
                return;
        }

        $this->braceIsPrefixed = true;
        $this->beginIsConsumed = true;
    }

    function &split($lexeme)
    {
        global $dotsOutsidePairedBrackets;
        $arr = [];
        $start = 0;
        foreach (std\matchAll("/($dotsOutsidePairedBrackets)|\\(($dotsOutsidePairedBrackets)\\)/", $lexeme) as [&$m,$index]) {
            if ($index > $start)
                $arr[] = std\substring($lexeme, $start, $index);

            if ($m[1])
                $arr[] = ['dot' => $m[1]];
            else if ($m[2])
                $arr[] = ['dot' => $m[2]];
            else
                $arr[] = $m[0];

            $start = $index + strlen($m[0]);
        }

        if ($start < strlen($lexeme))
            $arr[] = std\substring($lexeme, $start);

        return $arr;
    }

    function process($lexeme)
    {
        $regexp = [];
        foreach ($this->split($lexeme) as &$piece) {
            if (is_array($piece)) {
                $dot = $piece['dot'];
                $regexp[] = balancedBraces($dot);
                if (! preg_match('/[*?]$/', $dot)) {
                    $this->braceIsPrefixed = true;
                    $this->beginIsConsumed = true;
                }
            } else {
                if (preg_match("/[\\\\]\\d+/", $piece)) {
                    $regexp[] = $piece;
                    $this->braceIsPrefixed = false;
                    $this->beginIsConsumed = true;
                }
                else {
                    $expr = Lexeme::construct($piece)->regexp($this->braceIsPrefixed, $this->beginIsConsumed, $this->projective);
                    $expr = Regex::compile($expr);
                    $expr->rewrite(true);
                    $regexp[] = "$expr";
                    if ($expr->match_length() !== 0) {
                        $this->braceIsPrefixed = false;
                        $this->beginIsConsumed = true;
                    }
                }
            }
        }

        return implode('', $regexp);
    }

    function captureParenthesis($regexp)
    {
        global $braceInBrackets;
        return preg_replace_callback("/(\((\?:)?((?:[\\\\][{}]|\||$braceInBrackets)+)\))|[\\\\][{}][*+?]|(?<!\(\?<=)(?<!\(\?=)\\[[{}]+\\][*+?]?/", function (&$m) {
            if (count($m) >= 2 && $m[1]) {
                if ($m[2]) {
                    return "($m[3])";
                } else {
                    return $m[0];
                }
            } else {
                return "($m[0])";
            }
        }, $regexp);
    }

    function transform_negative_braces_que($s) {
        return preg_replace_callback("/(?<![\\\\])!(\{+|\}+)\?/", function(&$m) {
            $count = strlen($m[1]);
            $brace = $m[1][0];
            foreach (std\range(1, $count - 1) as $i) {
                $regex[] = str_repeat($brace, $i);
            }
            
            if ($brace == '{') {
                $regex[] = "$m[1][{}]+";
                $regex[] = "}[{}]*";
            }
            else {
                $regex[] = "[{}]+$m[1]";
                $regex[] = "[{}]*{";
            }
            
            $regex = implode("|", $regex);
            return "(?:$regex)";
        }, $s);
    }
    
    public function functional_substitution($s){
        $s = functional_substitution($s);

        $s = $this->transform_negative_braces_que($s);
        
        $s = transform_negative_braces($s);
                
        if (preg_match("/(?<![\\\\])!(\{+|\}+)/", $s)) {
            $s = transform_for_balanced_braces($s);
        }
        
        return $s;
    }

    public function segment($s)
    {
        global $regexToSegment;
        $s = $this->functional_substitution($s);
        $infixList = [];
        $infixIndices = [];

        $start = 0;
        $tokens = [];
        $logicalGroupCount = 0;
        $physicalGroupCount = 0;

        $indexMapping = [];

        foreach (std\matchAll($regexToSegment, $s) as [&$m,$index]) {
            $part = $m[0];
            if ($index > $start)
                $tokens[] = std\substring($s, $start, $index);

            $start = $index + strlen($part);
            [$part,$indexMap,$gLogicalCount,$gPhysicalCount] = segment($part);

            if (! $gPhysicalCount) {
                if (! preg_match("/[\\\\]\\d+/", $part)) {
                    ++ $gPhysicalCount;
                }
            }

            foreach ($indexMap as $key => $value) {
                $key += $logicalGroupCount;
                $value += $physicalGroupCount;
                $indexMapping[$key] = $value;
            }

            $logicalGroupCount += $gLogicalCount;
            $physicalGroupCount += $gPhysicalCount;

            $tokens[] = $part;
        }

        if ($start < strlen($s)) {
            $tokens[] = std\substring($s, $start);
        }

        return [implode("", $tokens),$indexMapping];
    }

    public function halve(&$infixIndices, &$substituentList, &$infixList, $i, $j) {
        [$infixList[$j],$rest] = std\halve($infixList[$j], strlen($substituentList[$i]));
        $start = $infixIndices[$j]['start'];
        $end = $infixIndices[$j]['end'];
        $mid = $start + strlen($infixList[$j]);
        
        $infixIndices[$j]['end'] = $mid;
        $infixIndices[$j]['segment'] = true;
        
        std\array_insert($infixList, $j + 1, $rest);
        std\array_insert($infixIndices, $j + 1, ['start' => $mid,'end' => $end,'segment' => true,'lexeme' => true]);
    }

    public function generate_regexp_for_substituent($substituent)
    {
        global $regexToSegment;
        [$substituent] = $this->segment($substituent);
        $substituent = preg_replace_callback("/(?<=[\\\\])\\d+/", fn (&$m) => $this->indexMapping[$m[0][0]], $substituent);

        $infixList = [];
        $infixIndices = [];
        foreach (std\matchAll($regexToSegment, $this->regulation) as [&$m,$start]) {
            $part = $m[0];

            $end = $start + strlen($part);

            if (! $part || std\fullmatch("/[()]+/", $part))
                continue;

            $lexeme = $m[1] ? false : true;
            global $leftParenthesisForCapture;
            foreach (std\replaceAll("/${leftParenthesisForCapture}[^()]+\\)/", function (&$m) {
                [[$mText], $start] = $m;
                $end = $start + strlen($mText);
                return ["text" => $mText,'start' => $start,'end' => $end,"group" => true];
            }, $part, false) as &$item) {
                $item['start'] += $start;
                $item['end'] += $start;

                $text = std\pop($item, 'text');
                $infixList[] = $text;
                if (std\pop($item, 'group')) {
                    $item['lexeme'] = $lexeme;
                } else {
                    $item['lexeme'] = std\fullmatch("/[\\\\]\\d+/", $text) ? false : $lexeme;
                }
                $infixIndices[] = $item;
            }
        }

        $substituentList = [];
        $start = 0;
        foreach (std\matchAll($regexToSegment, $substituent) as [&$m,$index]) {
            $part = $m[0];
            if ($index > $start)
                $substituentList[] = ['text' => std\substring($substituent, $start, $index)];

            $start = $index + strlen($part);
            if (! $part)
                continue;

            foreach (std\replaceAll("/${leftParenthesisForCapture}[^()]+\\)/", fn (&$m) => $m[0][0], $part, false) as &$item) {
                $substituentList[] = is_string($item) ? $item : $item['text'];
            }
        }

        $text = std\substring($substituent, $start);
        if ($text)
            $substituentList[] = ['text' => std\substring($substituent, $start)];

        $j = 0;
        $diff = 0;
        for (; $j < count($infixList); ++ $j) {
            $i = std\indexOf($substituentList, $infixList[$j]);
            if ($i < 0) {
                foreach (std\range(count($substituentList)) as $i) {
                    if (is_string($substituentList[$i])) {
                        if (str_starts_with($substituentList[$i], $infixList[$j])) {
                            $substituentList[$i] = std\substring($substituentList[$i], strlen($infixList[$j]));
                            std\array_insert($substituentList, $i, $infixList[$j]);
                            break;
                        }
                        
                        if (str_starts_with($infixList[$j], $substituentList[$i])) {
                            $this->halve($infixIndices, $substituentList, $infixList, $i, $j);
                            break;
                        }
                        
                        if (preg_match("/^\((.+)\)$/", $infixList[$j], $m) && $m[1] == $substituentList[$i]) {
                            break;
                        }
                        
                        if (str_starts_with($infixList[$j], '('.$substituentList[$i].')')) {
                            $substituentList[$i] = '('.$substituentList[$i].')';
                            $this->halve($infixIndices, $substituentList, $infixList, $i, $j);
                            break;
                        }
                    }
                }
            }
            elseif (preg_match("/^\((.+)\)$/", $infixList[$j], $m)){
                $i_ = std\indexOf($substituentList, $m[1]);
                if ($i_ >= 0 && $i_ < $i){
                    $i = $i_;
                }
            }
            elseif ($i > 0 && count($infixList) > count($substituentList)) {
                foreach (std\range(0, $i) as $i_) {
                    if (is_string($substituentList[$i_])) {
                        if (str_starts_with($substituentList[$i_], $infixList[$j])) {
                            $substituentList[$i_] = std\substring($substituentList[$i_], strlen($infixList[$j]));
                            std\array_insert($substituentList, $i_, $infixList[$j]);
                            $i = $i_;
                            break;
                        }
                    }
                }
            }

            if (preg_match("/[\\\\](\\d+)/", $infixList[$j], $m)) {
                $substituentList[$i] = "$" . $m[1];
                ++ $diff;
            } else {
                $substituentList[$i] = "$" . ($j + 1 - $diff);
            }
        }

        foreach (std\range(count($substituentList)) as $i) {
            if (is_array($substituentList[$i]))
                $substituentList[$i] = $substituentList[$i]['text'];
        }

        if (std\array_any(fn (&$args) => array_key_exists('segment', $args), $infixIndices)) {
            $regulation = '';
            $start = 0;
            foreach (std\zip($infixIndices, $infixList) as [$indices,$text]) {
                if ($indices['start'] > $start)
                    $regulation .= std\substring($this->regulation, $start, $indices['start']);

                if (array_key_exists('segment', $indices) && !(Regex::compile($text)->arg instanceof RegexGroupCaptured))
                    $regulation .= "($text)";
                else
                    $regulation .= $text;

                $start = $indices['end'];
            }

            $regulation .= std\substring($this->regulation, $start);

            $this->regulation = $regulation;
        }

        $prevTokenIndex = 0;
        $index = 0;

        foreach ($substituentList as $s) {
            if (preg_match("/^\\$(\\d+)$/", $s, $m)) {
                $m = (int)$m[1];
                if (! $infixIndices[$m - 1]['lexeme']) {
                    continue;
                }

                if ($prevTokenIndex && ! in_array($m, $this->indexMapping)) {
                    assert($m > $prevTokenIndex, new Error("resulting in a non-projective tree"));
                }

                $prevTokenIndex = $m;
            } else {
                assert(preg_match("/^[{}]+$/", $s), new Error("resulting in an erroneous tree"));
            }
        }

        return implode('', $substituentList);
    }

    public function substitute($infix)
    {
        $count = 1;
        foreach ($this->backwardSubstitution as &$backwardSubstitution) {
            [$s, $totalLength, $type] = $backwardSubstitution;

            switch ($type) {
            case '*':
            case '+':
            case '?':
                //captured group with [*+?]
                $s = remove_capture($this->construct_regex($this->functional_substitution($s)));
                $infix = str_replace("((?:\{[^{}]*\})$type)", "((?:$s)$type)", $infix, $count);
                break;
//             case '=':
//             case '!':
//             case '<=':
//             case '<!':
//                 //lookAround
//                 $s = functional_substitution($s);
//                 $infix = str_replace("(?${type}[^\s{}]*)", $s, $infix, $count);
//                 break;
            }
        }

        return $infix;
    }
}

class SyntaxMatcher
{

    public $infix;

    public $infix_replacement;

    public function __get($vname)
    {
        switch ($vname) {
            case 'regexp':
                return $this->infix;
            default:
                return null;
        }
    }

    public function __construct($pseudo_x, $substituent, $projective = true, $scan=false)
    {
        $filter = new SyntaxFilterExpression($pseudo_x, $projective, $scan);

        if ($scan) {
            $backwardSubstitution = null;
            $this->indexMapping = $filter->indexMapping;
        }
        else {
            [$backwardSubstitution,$substituent] = remove_capture_unnamed($substituent);
        }

        $this->infix_replacement = $filter->generate_regexp_for_substituent($substituent);
        $this->infix = $filter->captureParenthesis($filter->construct_regex($filter->regulation));

        if ($backwardSubstitution) {
            $this->infix = $filter->substitute($this->infix);
        }
    }

    function transform_text($text_original)
    {
        return $text_original . replace($this->text, $this->text_replacement);
    }

    public static function transform($infix, $scan=false)
    {
        $filter = new SyntaxFilterExpression($infix, true, $scan);

        $infix = $filter->captureParenthesis($filter->construct_regex($filter->regulation));
        if ($filter->backwardSubstitution) {
            $infix = $filter->substitute($infix);
        }
        if ($scan) {
            return [$infix, array_values($filter->indexMapping)];
        }
        return $infix;
    }
}

function transform_infix($old, $new = null, $scan=false, $projective=true)
{
    // $binary = preg_match("/(?!=[\\\\])[\\\\]\\d+/", $old) ? true : false;
    $binary = preg_match("/(?![\\\\])[\\\\]\\d+/", $old) ? true : false;
    if ($new === null) {
        if ($scan) {
            [$infix, $indices] = SyntaxMatcher::transform($old, $scan);
            $indices[] = 0;
        }
        else {
            $infix = SyntaxMatcher::transform($old);
            $indices = 0;
        }
        
        return [$infix,null, $indices, $binary];
    }

    $syntaxMatcher = new SyntaxMatcher($old, $new, $projective, $scan);
    $infix = $syntaxMatcher->infix;
    $infix_replacement = $syntaxMatcher->infix_replacement;

    if ($scan) {
        $indices = array_values($syntaxMatcher->indexMapping);
        $indices[] = 0;
        return [$infix,$infix_replacement,$indices, $binary];
    }
    
    return [$infix,$infix_replacement,$binary];
}

?>