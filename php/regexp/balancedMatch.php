<?php
// a legal open bracket is represented by
$openBracket = "(?<![\\\\])\\[";

// a non-open-bracket char is represented by :
$nonOpenBracket = "(?:(?<=[\\\\])\\[|[^\\[])";

// a non-bracket char is represented by :
$nonBracket = "(?:[^\\[\\]]|(?<=[\\\\])\\[|(?<=[\\\\])\\])";

// a legal Close bracket is represented by
$CloseBracket = "(?<![\\\\])\\]";

// a non-Close-bracket char is represented by :
$nonCloseBracket = "(?:(?<=[\\\\])\\]|[^\\]])";

// any symbol to be matched outside the paired brackets:
// firstly, a legal open bracket is detected and, before the legal open bracket there are no brackets;
// .(?=$nonBracket*$openBracket)

// secondly, no legal Close brackt is detected: //all not
// .(?=$nonCloseBracket*$)
// put together:
$outsidePairedBrackets = "(?=$nonBracket*$openBracket|$nonCloseBracket*$)";

// symbol inside the paired brackets:
$insidePairedBrackets = "(?=$nonOpenBracket*$CloseBracket)";

$leftParenthesisForCapture = "(?<![\\\\])\\((?!(?:\\?<=|\\?<!|\\?=|\\?!|\\?:))$outsidePairedBrackets";

function recursive_construct($parentheses, $depth)
{
    $mid = strlen($parentheses) / 2;
    $start = substr($parentheses, 0, $mid);
    $end = substr($parentheses, $mid);

    if (need_escape($start)) {
        $start = "\\" . $start;
        $end = "\\" . $end;
    }

    if ($depth == 1)
        return "${start}[^$parentheses]*$end";

    return "${start}[^$parentheses]*(?:" . recursive_construct($parentheses, $depth - 1) . "[^$parentheses]*)*$end";
}

function recursive_construct_extended($parentheses, $depth, $lookBehindForBackslash=true)
{
    $mid = strlen($parentheses) / 2;
    $start = substr($parentheses, 0, $mid);
    $end = substr($parentheses, $mid);
    
    $need_escape = need_escape($start);
    if ($need_escape) {
        $start = "\\" . $start;
        $end = "\\" . $end;
    }

    if ($need_escape) {
        global $insidePairedBrackets, $outsidePairedBrackets;
        $nonParenthesesChars[] = "[^$parentheses]";
        if ($lookBehindForBackslash)
            $nonParenthesesChars[] = "(?<=[\\\\])[$parentheses]";

        $nonParenthesesChars[] = "[$parentheses]$insidePairedBrackets";

        $nonParenthesesChars = implode('|', $nonParenthesesChars);
        $nonParenthesesChars = "(?:$nonParenthesesChars)*";

        $start = "$start$outsidePairedBrackets";
        $end = "$end$outsidePairedBrackets";

        if ($lookBehindForBackslash) {
            $start = "(?<![\\\\])$start";
            $end = "(?<![\\\\])$end";
        }
    }
    else {
        $nonParenthesesChars = "[^$parentheses]*";
    }
     
    return $depth == 1? "${start}$nonParenthesesChars$end": "${start}$nonParenthesesChars(?:" . recursive_construct_extended($parentheses, $depth - 1, $lookBehindForBackslash) . "$nonParenthesesChars)*$end";
}

function balancedGroups($parentheses, $depth, $multiple = '*')
{
    $regex = recursive_construct($parentheses, $depth);
    if ($multiple)
        return "((?:$regex)$multiple)";
    else
        return "($regex)";
}

function balancedGroupsExtended($parentheses, $depth, $multiple = '*', $lookBehindForBackslash=true)
{
    $regex = recursive_construct_extended($parentheses, $depth, $lookBehindForBackslash);
    if ($multiple)
        return "((?:$regex)$multiple)";
    else
        return "($regex)";
}

function need_escape($s)
{
    switch ($s) {
        case "(":
        case "[":
        case "{":
            
        case ")":
        case "]":
        case "}":
            return true;
        default:
            return false;
    }
}

function balancedBraces($depth)
{
    $multiple = '';
    if (is_string($depth)) {
        $back = $depth[-1];
        if ($back == '.') {
            $depth = strlen($depth);
        } else {
            $multiple = $back;
            $depth = strlen($depth) - 1;
        }

        $depth = 1 << $depth - 1;
    }

    return balancedGroups("{}", $depth, $multiple);
}

function balancedParentheses($depth, $multiple = '')
{
    return balancedGroups("()", $depth, $multiple);
}

function balancedParenthesesExtended($depth, $multiple = '')
{
    return balancedGroupsExtended("()", $depth, $multiple, true);
}

function balancedBracesExtended($depth, $multiple = '')
{
    return balancedGroupsExtended("{}", $depth, $multiple, false);
}

function balancedParenthesesUnicode($depth)
{
    return balancedGroups("（）", $depth);
}

function balancedBrackets($depth, $multiple = '*')
{
    return balancedGroups("[]", $depth, $multiple);
}

function balancedAngleBrackets($depth, $multiple = '*')
{
    return balancedGroups("<>", $depth, $multiple);
}

function balancedQuotes($depth)
{
    return balancedGroups("‘’", $depth);
}

function balancedDoubleQuotes($depth)
{
    return balancedGroups("“”", $depth);
}

function balancedBracketsUnicode($depth)
{
    return balancedGroups("【】", $depth);
}

function balancedFrenchQuotes($depth)
{
    return balancedGroups("《》", $depth);
}

function balancedSemiQuotes($depth)
{
    return balancedGroups("「」", $depth);
}

function balancedSemiBoldQuotes($depth)
{
    return balancedGroups("『』", $depth);
}

function remove_lookaround($regex)
{
    return preg_replace("/\\(\\?=[^(]+?\\)|\\(\\?![^(]+?\\)|\\(\\?<=[^(]+?\\)|\\(\?<![^(]+?\\)/", "", $regex);
}

function remove_capture($regex)
{
    global $leftParenthesisForCapture;
    // (?<=), (?<!), (?=), (?!), (?:)
    return preg_replace("/$leftParenthesisForCapture/", "(?:", $regex);
}

function detect_capture($regex)
{
    global $leftParenthesisForCapture;
    // (?<=), (?<!), (?=), (?!), (?:)
    return preg_match("/$leftParenthesisForCapture/", $regex);
}

function remove_capture_unnamed($s, $namedCapture = false)
{
    // (?<=), (?<!), (?=), (?!), (?:)
    global $balancedParenthesesExtended;
    if (! $namedCapture)
        $namedCapture = preg_match("/[\\\\]\\d+/", $s) ? true : false;

    $start = 0;
    $tokens = [];
    $groupCount = 0;
    
    foreach (std\matchAll($balancedParenthesesExtended, $s) as [&$m, $index]) {
        if ($index > $start)
            $tokens[] = std\substring($s, $start, $index);

        $start = $index + strlen($m[0]);

        if (preg_match("/[{}]/", $m[0])) {
            if ($start < strlen($s) && std\contains("*+?", $s[$start])) {
                $tokens[] = [
                    'group' => $m[0] . $s[$start]
                ];
                ++ $groupCount;
                ++ $start;
            }
            elseif (preg_match("/^\(([{}]|\\[[{}]+\\][*+?]?|\|)+\)$/", $m[0])) {
                $tokens[] = [
                    'brace' => $m[0]
                ];
                ++ $groupCount;
            }
            elseif (preg_match("/^\(\?(<?[!=])/", $m[0], $lookAroundType)) {
                $tokens[] = [
                    'lookAround' => $m[0],
                    'type' => $lookAroundType[1],
                ];
                ++ $groupCount;
            }
            else {
                $tokens[] = $m[0];
            }
        } else {
            $tokens[] = $m[0];
        }
    }

    if (strlen($s) > $start)
        $tokens[] = std\substring($s, $start);

    if ($groupCount == 0) {
        $s = implode("", $tokens);
        if (! $namedCapture)
            $s = remove_capture($s);
        return [
            null,
            $s
        ];
    } else {
        $groups = [];
        $backSubstition = [];
        $totalLength = 0;
        foreach ($tokens as $s) {
            if (is_string($s)) {
                if (! $namedCapture)
                    $s = remove_capture($s);
                $groups[] = $s;
                $totalLength += strlen($s);
            } elseif (array_key_exists('group', $s)) {
                $group = $s['group'];
                [$innerBackSubstition, $s] = remove_capture_unnamed(std\substring($group, 1, - 2), $namedCapture);
                if ($innerBackSubstition) {
                    throw new Exception("innerBackSubstition unimplemented yet!");
                    [$s, $innerGroup] = $s;
                    $groups[] = $s;
                } else {
                    $multiple = $group[-1];
                    $groups[] = "." . $multiple;
                    $backSubstition[] = [
                        $s,
                        $totalLength,
                        $multiple
                    ];
                    $totalLength += 2;
                }
            } elseif (array_key_exists('brace', $s)) {
                $s = $s['brace'];
                $groups[] = $s;
                $totalLength += strlen($s);                
            } else {
                $group = $s['lookAround'];
                $group = preg_replace_callback("/[{}]/", fn(&$m) => '\\x'. dechex(ord($m[0])), $group);
                $groups[] = $group;
                $totalLength += strlen($group);
            }
        }

        return [
            $backSubstition,
            implode("", $groups)
        ];
    }
}

$balancedParenthesesExtended = balancedParenthesesExtended(16);
$balancedBracesExtended = balancedBracesExtended(16);

$anyRegexp = std\substring($balancedParenthesesExtended, 1, -1);
$anyRegexp = "(?:$anyRegexp|[^()]|[\\\\][()])+";

function segment($s)
{
    global $balancedParenthesesExtended, $leftParenthesisForCapture;
    $indexMapping = [];
    $logicalGroupCount = 0;
    $physicalGroupCount = 0;

    $start = 0;
    $tokens = [];
    $previousisGroup = false;
    $hit = false;
    foreach (std\matchAll("/$balancedParenthesesExtended|([\\\\]\\d+)/", $s) as [&$m, $index]) {
        $mText = $m[0];
        if ($index > $start) {
            if ($hit) {
                $tokens[] = ")";
                ++ $physicalGroupCount;
                $previousisGroup = true;
            }
            $tokens[] = std\substring($s, $start, $index);
            $hit = false;
        }

        $end = $index + strlen($mText);
        if ($m[2]) {
            if ($index) {
                $tokens[count($tokens) - 1] = "(" . end($tokens) . ")";
                ++ $physicalGroupCount;
                $previousisGroup = true;
            }

            $rest = std\substring($s, $end);
            if ($rest) {
                $mText .= "(";
                $hit = true;
                $previousisGroup = false;
            }
        } else {
            if (preg_match("/^$leftParenthesisForCapture/", $mText)) {
                ++ $logicalGroupCount;
                ++ $physicalGroupCount;

                [$mText, $innerIndexMapping, $innerLogicalGroupCount, $innerPhysicalGroupCount] = segment(std\substring($mText, 1, - 1));

                foreach ($innerIndexMapping as $key => $value) {
                    $key += $logicalGroupCount;
                    $value += $physicalGroupCount;
                    $indexMapping[$key] = $value;
                }

                if ($index && !$previousisGroup) {
                    if ($hit) {
                        $tokens[count($tokens) - 1] = end($tokens) . ")";
                        $hit = false;
                    }
                    else {
                        $tokens[count($tokens) - 1] = "(" . end($tokens) . ")";
                    }

                    ++ $physicalGroupCount;
                }

                $rest = std\substring($s, $end);
                if ($rest) {
                    if (preg_match("/^[*+?]/", $rest)) {
                        $mText = "((?:$mText)$rest[0])";
                        $rest = std\substring($rest, 1);
                        ++$end;
                    }
                    else {
                        $mText = "($mText)";
                    }

                    if ($rest && ! preg_match("/^$leftParenthesisForCapture/", $rest)) {
                        $mText .= "(";
                        $hit = true;
                        $previousisGroup = false;
                    }
                    else {
                        $previousisGroup = true;
                    }
                }
                else {
                    $mText = "($mText)";
                    $previousisGroup = true;
                }

                $indexMapping[$logicalGroupCount] = $physicalGroupCount;
                $logicalGroupCount += $innerLogicalGroupCount;
                $physicalGroupCount += $innerPhysicalGroupCount;
            }
            else {
                $previousisGroup = false;
                
                $rest = std\substring($s, $end);
                if ($rest) {
                    if (preg_match("/^[*+?]/", $rest)) {
                        $mText .= $rest[0];
                        ++$end;
                    }
                }
                
                if ($hit) {
                    $mText .= ")";
                    ++ $physicalGroupCount;
                    $previousisGroup = true;
                    $hit = false;
                }
            }
        }

        $tokens[] = $mText;

        $start = $end;
    }

    if ($start < strlen($s)) {
        $s = std\substring($s, $start);
        $tokens[] = $s;
        if ($hit) {
            ++ $physicalGroupCount;
            $tokens[] = ")";
        }
    }

    return [
        implode("", $tokens),
        $indexMapping,
        $logicalGroupCount,
        $physicalGroupCount
    ];
}

function transform_negative_braces($s) {
    return preg_replace_callback("/(?<![\\\\])!(\{+|\}+)/", function (&$m) {
        $count = strlen($m[1]);
        $brace = $m[1][0];
        foreach (std\range(1, $count) as $i) {
            $regex[] = str_repeat($brace, $i);
        }

        if ($brace == '{') {
            $regex[] = "$m[1][{}]+";
            $regex[] = "}[{}]*";
        } else {
            $regex[] = "[{}]+$m[1]";
            $regex[] = "[{}]*{";
        }

        $regex = implode("|", $regex);
        return "(?:$regex)";
    }, $s);
}

function transform_for_balanced_braces($s)
{
    global $balancedBracesExtended;
    $indexMapping = [];
    $logicalGroupCount = 0;
    $physicalGroupCount = 0;
    
    $start = 0;
    $tokens = [];
    $hit = false;
    foreach (std\matchAll("/$balancedBracesExtended/", $s) as [&$m, $index]) {
        if ($index > $start) {
            $tokens[] = transform_negative_braces(std\substring($s, $start, $index));
        }
        
        $tokens[] = $m[0];
        
        $start = $index + strlen($m[0]);
    }
    
    if ($start < strlen($s)) {
        $tokens[] = transform_negative_braces(std\substring($s, $start));
    }
    
    return implode("", $tokens);
}

?>