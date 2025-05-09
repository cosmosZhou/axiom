<?php
require_once '../std.php';
require_once '../lean/compile.php';

function tagged_latex($prop, $tag)
{
    $tag = latex_tag($tag);
    return $prop->toLatex() . "\\tag*{\$$tag\$}";
}

function parse_parenthesis($lean)
{
    $colon = $lean->arg;
    if ($colon instanceof LColon) {
        [$tag, $prop] = $colon->args;
        return tagged_latex($prop, $tag);
    }
}

function parse_colon($lean)
{
    if ($lean->rhs instanceof LCaret) {
        $lean = $lean->lhs;
        if ($lean instanceof LParenthesis) {
            $colon = $lean->arg;
            if ($colon instanceof LColon) {
                $token = $colon->lhs;
                if ($token instanceof LToken) {
                    $old_token = $token->arg;
                    $token->arg .= ' :';
                    $latex = parse_parenthesis($lean);
                    $token->arg = $old_token;
                    if ($latex)
                        return $latex;
                }
            }
        }
    }
}

function parse_assign($lean)
{
    [$prop, $tag] = $lean->args;
    if ($tag instanceof L_by && ($stmt = $tag->arg) instanceof LStatements && count($stmt->args) == 1 && $stmt->args[0] instanceof LCaret)
        $tag->arg = $stmt->args[0];
    return tagged_latex($prop, ":= " . $tag);
}
function toLatex($lean)
{
    if (end($lean->args) instanceof LCaret)
        array_pop($lean->args);
    $count = count($lean->args);
    if ($count > 1) {
        $result = [];
        foreach (std\range($count - 1) as $i) {
            $code = $lean->args[$i];
            if ($code instanceof LParenthesis) {
                $latex = parse_parenthesis($code);
                if ($latex) {
                    $result[] = [
                        'lean' => "$code",
                        'latex' => $latex,
                    ];
                } else {
                    $result[] = [
                        'lean' => "$code",
                    ];
                }
            }
            else {
                $result[] = [
                    'lean' => "$code",
                ];
            }
        }
        $end = end($lean->args);
        if ($end instanceof LColon)
            $latex = parse_colon($end);
        elseif ($end instanceof LAssign)
            $latex = parse_assign($end);
        elseif ($end instanceof LParenthesis)
            $latex = parse_parenthesis($end);
        else
            $latex = null;
        if ($latex) {
            $result[] = [
                'lean' => "$end",
                'latex' => $latex,
            ];
            return $result;
        }
    }
    $latex = null;
    if ($count == 1) {
        $lean = $lean->args[0];
        if ($lean instanceof LParenthesis)
            $latex = parse_parenthesis($lean);
        elseif ($lean instanceof LAssign)
            $latex = parse_assign($lean);
        elseif ($lean instanceof LColon)
            $latex = parse_colon($lean);
    }
    if (!$latex) 
        $latex = $lean->toLatex();
    return ['latex' => $latex];
}

try {
    echo std\encode(toLatex(compile($_POST['lean'] . "\n")));
} catch (Exception $e) {
    echo std\encode(['error' => $e->getMessage()]);
}
