<?php

require_once dirname(__file__) . '/../std.php';
ini_set('xdebug.max_nesting_level', 1024);

$token2classname = [
    '+' => 'LeanAdd',
    '-' => 'LeanSub',
    '*' => 'LeanMul',
    '/' => 'LeanDiv',
    '%' => 'LeanMod',
    '×' => 'LeanTimes',
    '•' => 'LeanSMul',
    '⊙' => 'LeanODot',
    '⊗' => 'LeanOTimes',
    '⊕' => 'LeanOPlus',
    '⊖' => 'LeanOMinus',
    '⊘' => 'LeanODiv',
    '⊚' => 'LeanOCirc',
    '⊛' => 'LeanOStar',
    '⊜' => 'LeanOEq',
    '⊝' => 'LeanONeg',
    '⊞' => 'LeanBoxPlus',
    '⊟' => 'LeanBoxMinus',
    '⊠' => 'LeanBoxTimes',
    '&' => 'LeanBitAnd',
    '|' => 'LeanBitOr',
    '^' => 'LeanBitXor',
    '<<' => 'LeanSHL',
    '>>' => 'LeanSHR',
    '||' => 'LeanLogicOr',
    '&&' => 'LeanLogicAnd',
    '∨' => 'LeanOr',
    '∧' => 'LeanAnd',
    '∪' => 'LeanUnion',
    '∩ ' => 'LeanIntersection'
];

abstract class Lean implements JsonSerializable
{

    public $parent = null;
    public $indent;

    public function __construct($indent, $parent = null)
    {
        $this->indent = $indent;
        $this->parent = $parent;
    }

    public function append_by($caret)
    {
        return $caret->append('LeanBy');
    }

    public function append_cases($caret)
    {
        return $caret->append('LeanCases');
    }
    public function append_case($caret)
    {
        return $caret->append('LeanCase');
    }
    public function append_by_contra($caret)
    {
        return $caret->append('LeanByContra');
    }
    public function append_rw($caret)
    {
        return $caret->append('LeanRw');
    }
    public function append_simp($caret)
    {
        return $caret->append('LeanSimp');
    }
    public function append_space($caret)
    {
        return $caret;
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        return $this->parent->append_newline($this, $newline_count, $indent);
    }

    public function append_end($caret)
    {
        return $this->parent->append_end($this);
    }

    public function append($new)
    {
        return $this->parent->append($new);
    }

    public function __clone()
    {
        $this->parent = null;
    }

    public function append_binary($type)
    {
        $parent = $this->parent;
        if ($type::$input_precedence > $parent->stack_precedence) {
            $new = new LeanCaret($this->indent);
            $parent->replace($this, new $type($this, $new, $this->indent));
            return $new;
        } else
            return $this->parent->append_binary($type);
    }
    
    public function append_arithmetic($token)
    {
        global $token2classname;
        return $this->append_binary($token2classname[$token]);
    }
    public function append_or()
    {
        $parent = $this->parent;
        return LeanOr::$input_precedence > $parent->stack_precedence ? $this->append_multiple("LeanOr", new LeanCaret($this->indent)) : $parent->append_or();
    }

    public function append_multiple($Type, $caret)
    {
        $parent = $this->parent;
        if ($parent instanceof $Type) {
            $parent->push($caret);
        } else
            $parent->replace($this, new $Type([$this, $caret], $parent));

        return $caret;
    }

    public function push_token($word)
    {
        return $this->append(new LeanToken($word, $this->indent));
    }

    public function append_token($caret, $word)
    {
        return $caret->push_token($word);
    }

    public function append_comma($caret)
    {
        return $this->parent->append_comma($this);
    }

    public function append_semicolon()
    {
        return $this->parent->append_semicolon();
    }

    public function append_colon($caret)
    {
        return $caret->append_binary('LeanColon');
    }

    public function append_assign($caret)
    {
        return $caret->append_binary('LeanAssign');
    }
    public function append_bitor($caret)
    {
        return $caret->append_arithmetic('|');
    }

    public function append_unary($func)
    {
        $caret = new LeanCaret($this->indent);
        $this->append(new $func($caret, $this->indent));
        return $caret;
    }

    public function append_left($Type)
    {
        switch ($Type) {
            case 'LeanParenthesis':
            case 'LeanBracket':
            case 'LeanBrace':
                $indent = $this->indent;
                $caret = new LeanCaret($indent);
                $new = new $Type($caret, $indent);
                if ($this->parent instanceof LeanArgumentsSpaceSeparated)
                    $this->parent->push($new);
                else
                    $this->parent->replace($this, new LeanArgumentsSpaceSeparated([$this, $new], $indent));
                return $caret;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function append_left_parenthesis($caret)
    {
        return $caret->append_left('LeanParenthesis');
    }

    public function append_left_angle_bracket($caret)
    {
        return $caret->append_left('LeanAngleBracket');
    }

    public function append_left_bracket($caret)
    {
        return $caret->append_left('LeanBracket');
    }

    public function append_left_brace($caret)
    {
        return $caret->append_left('LeanBrace');
    }

    public function append_right_parenthesis()
    {
        return $this->parent->append_right_parenthesis();
    }

    public function append_right_angle_bracket()
    {
        return $this->parent->append_right_angle_bracket();
    }

    public function append_right_bracket()
    {
        return $this->parent->append_right_bracket();
    }

    public function append_right_brace()
    {
        return $this->parent->append_right_brace();
    }

    public function append_dot($caret)
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_minus()
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_quote()
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_operator($func)
    {
        return $this->parent->append_operator($func);
    }
    public function append_using()
    {
        return $this->parent->append_using();
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "root":
                return $this->parent->root;
        }
    }

    public function replace_args(&$select, $old, $new)
    {
        if (std\is_list($select)) {
            $i = std\indexOf($select, $old);
            if ($i >= 0) {
                $select[$i] = $new;
                if (!$new->parent)
                    $new->parent = $this;
                return true;
            }
        } elseif ($select === $old) {
            $select = $new;
            if (!$new->parent)
                $new->parent = $this;

            return true;
        }
    }
}

class LeanCaret extends Lean
{

    public function __toString()
    {
        return "";
    }

    public function append_line_comment($comment)
    {
        $parent = $this->parent;
        $parent->replace($this, new LeanLineComment($comment, $this->indent));
        $parent->push($this);
        return $this;
    }

    public function append($new)
    {
        if (is_string($new)) {
            $this->parent->replace($this, new $new($this, $this->indent));
            return $this;
        } else {
            $this->parent->replace($this, $new);
            return $new;
        }
    }

    public function jsonSerialize(): mixed
    {
        return "";
    }

    public function append_left($Type)
    {
        $this->parent->replace($this, new $Type($this, $this->indent));
        return $this;
    }
}

class LeanToken extends Lean
{
    public $arg;

    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->arg = $arg;
    }

    public function append_quote()
    {
        $this->arg .= "'";
        return $this;
    }

    public function __toString()
    {
        $indent = $this->parent instanceof LeanArgumentsCommaNewLineSeparated ? str_repeat(' ', $this->indent) : '';
        return $indent . $this->arg;
    }

    public function push_token($word)
    {
        $new = new LeanToken($word, $this->indent);
        $this->parent->replace($this, new LeanArgumentsSpaceSeparated([$this, $new], $this->indent));
        return $new;
    }

    public function append($new)
    {
        return $this->parent->append($new);
    }

    public function jsonSerialize(): mixed
    {
        return $this->arg;
    }

    public function is_variable()
    {
        return std\fullmatch('/[a-zA-Z_][a-zA-Z_0-9]*/', $this->arg);
    }

    public function lower()
    {
        $this->arg = strtolower($this->arg);
        return $this;
    }
}

class LeanLineComment extends Lean
{

    public $arg;

    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->arg = $arg;
    }

    public function __toString()
    {
        return "-- $this->arg";
    }

    public function jsonSerialize(): mixed
    {
        return ["line_comment" => $this->arg];
    }
}

abstract class LeanArgs extends Lean
{
    public static $input_precedence = 2;
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 2;
            default:
                return parent::__get($vname);
        }
    }

    public $args;

    public function __construct($args, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }
    }

    public function replace($old, $new)
    {
        $i = std\index($this->args, $old);
        if ($i < 0)
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));

        if (is_array($new)) {
            array_splice($this->args, $i, 1, $new);
            foreach ($new as $el) {
                if (!$el->parent)
                    $el->parent = $this;
            }
        } else {
            $this->args[$i] = $new;
            if (!$new->parent)
                $new->parent = $this;
        }
    }

    public function removeChild($node)
    {
        $i = std\index($this->args, $node);
        if ($i < 0)
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        std\array_delete($this->args, $i);

        if (count($this->args) == 1) {
            [$arg] = $this->args;
            $parent = $this->parent;
            $parent->replace($this, $arg);
            $arg->parent = $parent;
        }
    }

    public function jsonSerialize(): mixed
    {
        return array_map(fn($arg) => $arg->jsonSerialize(), $this->args);
    }

    public function push($arg)
    {
        $this->args[] = $arg;
        $arg->parent = $this;
    }
}

abstract class LeanUnary extends LeanArgs
{
    public static $input_precedence = 2;
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 2;
            case "arg":
                return $this->args[0];
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case "arg":
                $this->args[0] = $val;
                break;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct([], $indent, $parent);
        $this->arg = $arg;
    }

    public function replace($old, $new)
    {
        assert($this->arg === $old, new Exception("assert failed: public function replace(\$old, \$new)"));
        $this->arg = $new;
    }

    public function __clone()
    {
        parent::__clone();
        $this->arg = clone $this->arg;
    }

    public function jsonSerialize(): mixed
    {
        return $this->arg->jsonSerialize();
    }
}


class LeanOperator extends LeanUnary
{
    public $func;
    public function __construct($func, $arg, $indent, $parent = null)
    {
        parent::__construct($arg, $indent, $parent);
        assert(is_string($func), new Exception("assert failed: public function __construct(\$func, \$arg, \$parent = null)"));
        $this->func = strtolower($func);
    }

    public function __toString()
    {
        return "$this->indent$this->func $this->arg";
    }

    public function jsonSerialize(): mixed
    {
        $func = $this->func;
        return [$func => $this->arg->jsonSerialize()];
    }
}

class LeanParenthesis extends LeanUnary
{
    public function __toString()
    {
        $parent = $this->parent;
        $indent = $parent instanceof LeanArgumentsNewLineSeparated ? str_repeat(' ', $this->indent) : '';
        return $indent . "($this->arg)";
    }

    public function append_right_parenthesis()
    {
        return $this;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -0.5;
            default:
                return parent::__get($vname);
        }
    }
}


class LeanAngleBracket extends LeanUnary
{
    public function __toString()
    {
        $parent = $this->parent;
        $indent = $parent instanceof LeanArgumentsNewLineSeparated ? str_repeat(' ', $this->indent) : '';
        return $indent . "⟨{$this->arg}⟩";
    }

    public function append_right_angle_bracket()
    {
        return $this;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -0.5;
            default:
                return parent::__get($vname);
        }
    }

    public function append_comma($caret)
    {
        $caret = new LeanCaret($this->indent);
        if ($caret instanceof LeanArgumentsCommaSeparated)
            $this->arg->push($caret);
        else
            $this->arg = new LeanArgumentsCommaSeparated([$this->arg, $caret], $this->indent);
        return $caret;
    }
}

abstract class LeanBinary extends LeanArgs
{
    public static $input_precedence = 2;

    public function __construct($lhs, $rhs, $indent, $parent = null)
    {
        parent::__construct([$lhs, $rhs], $indent, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "lhs":
                return $this->args[0];
            case "rhs":
                return $this->args[1];
            case "stack_precedence":
                return 2;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case "lhs":
                $this->args[0] = $val;
                break;
            case "rhs":
                $this->args[1] = $val;
                break;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function jsonSerialize(): mixed
    {
        return [$this->func => [$this->lhs->jsonSerialize(), $this->rhs->jsonSerialize()]];
    }
}

class LeanDot extends LeanBinary
{
    public function append_dot($caret)
    {
        return parent::append_dot($caret);
    }

    public function __toString()
    {
        $indent = $this->parent instanceof LeanArgumentsCommaNewLineSeparated ? str_repeat(' ', $this->indent) : '';
        return $indent . implode(".", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 6;
            case "func":
                return 'dot';
            default:
                return parent::__get($vname);
        }
    }

    public function append_left_parenthesis($caret)
    {
        return $this->parent->append_left_parenthesis($this);
    }

    public function append_token($caret, $word)
    {
        if ($caret instanceof LeanCaret)
            return parent::append_token($caret, $word);
        return $this->parent->append_token($this, $word);
    }

    public function push_token($word)
    {
        $new = new LeanToken($word, $this->indent);
        $this->parent->replace($this, new LeanArgumentsSpaceSeparated([$this, $new], $this->indent));
        return $new;
    }
}

class LeanColon extends LeanBinary
{
    public function __toString()
    {
        [$lhs, $rhs] = $this->args;
        if ($lhs instanceof LeanArgumentsNewLineSeparated) {
            $args = array_map(fn($arg) => "$arg", array_slice($lhs->args, 1));
            array_unshift($args, "{$lhs->args[0]}");
            $lhs = implode("\n", $args);
        }

        $sep = $rhs instanceof LeanCodeBlock ? "\n" : " ";
        return "$lhs :$sep$rhs";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 3;
            case "func":
                return 'colon';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanAssign extends LeanBinary
{
    public static $input_precedence = -0.4;
    public function __toString()
    {
        return implode(" := ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 4.2;
            case "func":
                return 'assign';
            default:
                return parent::__get($vname);
        }
    }
}

abstract class LeanBinaryBoolean extends LeanBinary
{
    public function __toString()
    {
        $indent = $this->parent instanceof LeanCodeBlock ? str_repeat(' ', $this->indent) : '';
        return $indent . implode(" $this->operator ", array_map(fn($arg) => "$arg", $this->args));
    }
}

abstract class LeanRelational extends LeanBinaryBoolean
{
    public static $input_precedence = 3.2;
}


class LeanGt extends LeanRelational
{

    public function __toString()
    {
        return implode(" > ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'gt';
            case 'operator':
                return '>';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanGe extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'ge';
            case 'operator':
                return '≥';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanLt extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'lt';
            case 'operator':
                return '<';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanLe extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'le';
            case 'operator':
                return '≤';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanEq extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'eq';
            case 'operator':
                return '=';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanNe extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'ne';
            case 'operator':
                return '≠';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanIff extends LeanBinaryBoolean
{
    public static $input_precedence = 3.7;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'iff';
            case 'operator':
                return '↔';
            default:
                return parent::__get($vname);
        }
    }
}

abstract class LeanArithmetic extends LeanBinary
{
    public static $input_precedence = 4.0;
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 3.2;
            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        return implode(" $this->operator ", array_map(fn($arg) => "$arg", $this->args));
    }

}


class LeanAdd extends LeanArithmetic
{
    public static $input_precedence = 4.2;
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'add';
            case 'operator':
                return '+';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanSub extends LeanArithmetic
{
    public static $input_precedence = 4.2;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'sub';
            case 'operator':
                return '-';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanMul extends LeanArithmetic
{
    public static $input_precedence = 4.5;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'mul';
            case 'operator':
                return '*';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanTimes extends LeanArithmetic
{
    public static $input_precedence = 4.5;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'times';
            case 'operator':
                return '×';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanSMul extends LeanArithmetic
{
    public static $input_precedence = 4.5;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'times';
            case 'operator':
                return '•';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanODot extends LeanArithmetic
{
    public static $input_precedence = 4.5;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'times';
            case 'operator':
                return '⊙';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanOTimes extends LeanArithmetic
{
    public static $input_precedence = 4.5;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'times';
            case 'operator':
                return '⊗';                
            default:
                return parent::__get($vname);
        }
    }
}


class LeanOPlus extends LeanArithmetic
{
    public static $input_precedence = 4.5;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'times';
            case 'operator':
                return '⊕';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanDiv extends LeanArithmetic
{
    public static $input_precedence = 4.5;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'div';
            case 'operator':
                return '/';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanBitAnd extends LeanArithmetic
{
    public static $input_precedence = 4.1;

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'bit_and';
            case 'operator':
                return '&';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanBitOr extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'bit_or';
            case 'operator':
                return '|';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanBitXor extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'bit_xor';
            case 'operator':
                return '^';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanSHL extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'shl';
            case 'operator':
                return '<<';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanSHR extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'shr';
            case 'operator':
                return '>>';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanMod extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'mod';
            case 'operator':
                return '%';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanIs extends LeanBinary
{
    public static $input_precedence = 3.5;

    public function __toString()
    {
        return implode(" is ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'is';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanIsNot extends LeanBinary
{
    public static $input_precedence = 3.5;

    public function __toString()
    {
        return implode(" is not ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'is_not';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanUnion extends LeanBinary
{
    public static $input_precedence = 0;
    public function __toString()
    {
        return implode(" ∪ ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'union';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanIntersection extends LeanBinary
{
    public static $input_precedence = 0;
    public function __toString()
    {
        return implode(" ∩ ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'intersection';
            default:
                return parent::__get($vname);
        }
    }
}

abstract class LeanLogic extends LeanBinary {}


class LeanLogicAnd extends LeanLogic
{
    public static $input_precedence = 1;

    public function __toString()
    {
        return implode(" && ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 3;
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof LeanAnd) {
            return ['logic_and' => [...$lhs['and'], $rhs]];
        }

        return ['logic_and' => [$lhs, $rhs]];
    }
}


class LeanLogicOr extends LeanLogic
{
    public static $input_precedence = 1;

    public function __toString()
    {
        return implode(" || ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0.9;
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof LeanOr) {
            return ['logic_or' => [...$lhs['or'], $rhs]];
        }

        return ['logic_or' => [$lhs, $rhs]];
    }
}

class LeanOr extends LeanLogic
{
    public static $input_precedence = 1;

    public function __toString()
    {
        return implode(" ∨ ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0.9;
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof LeanOr) {
            return ['or' => [...$lhs['or'], $rhs]];
        }

        return ['or' => [$lhs, $rhs]];
    }
}

class LeanAnd extends LeanLogic
{
    public static $input_precedence = 1;
    public function __toString()
    {
        return implode(" ∧ ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0.9;
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof LeanOr) {
            return ['or' => [...$lhs['or'], $rhs]];
        }

        return ['or' => [$lhs, $rhs]];
    }
}

class LeanFunction extends LeanArgs
{
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 3;
            case "func":
                return $this->args[0];
            case "parameters":
                return array_slice($this->args, 1);
            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        $args = implode(" ", array_map(fn($arg) => "$arg", $this->parameters));
        return str_repeat(" ", $this->indent) . "$this->func $args";
    }

    public function jsonSerialize(): mixed
    {
        $parameters = $this->parameters;
        if (count($parameters) == 1 && $parameters[0] instanceof LeanCaret) {
            $parameters = [];
        }
        return ["$this->func" => array_map(fn($arg) => $arg->jsonSerialize(), $parameters)];
    }

    public function append_comma($caret)
    {
        $new = new LeanCaret($this->indent);
        $this->push($new);
        return $new;
    }

    public function append_right_parenthesis()
    {
        return $this;
    }
}


class LeanCodeBlock extends LeanArgs
{
    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent > $indent)
            return parent::append_newline($caret, $newline_count, $indent);

        if ($this->indent < $indent) {
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } else {
            for ($i = 0; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->push($caret);
            }
            return $caret;
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -0.4;
            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        return implode("\n", array_map(fn($arg) => "$arg", $this->args));
    }

    public function jsonSerialize(): mixed
    {
        $args = parent::jsonSerialize();
        if (end($this->args) instanceof LeanCaret)
            array_pop($args);
        if (count($args) == 1)
            [$args] = $args;
        return $args;
    }
}


class LeanModule extends LeanCodeBlock
{
    public function __get($vname)
    {
        switch ($vname) {
            case "root":
                return $this;
            default:
                return parent::__get($vname);
        }
    }

    static function merge_proof($proof)
    {
        $proof = $proof->args;
        if ("$proof[0]" == '-- proof')
            array_shift($proof);
        $proof = array_map(fn($stmt) => "$stmt", $proof);
        for ($i = count($proof) - 1; $i >= 0; --$i) {
            if (preg_match("/^\n*$/", $proof[$i])) {
                $proof[$i - 1] .= "\n" . $proof[$i];
                array_splice($proof, $i, 1);
            }
        }
        return $proof;
    }

    public function render2vue()
    {
        $import = [];
        $open = [];
        $namespace = [];
        $date = [];
        $error = [];
        foreach ($this->args as $stmt) {
            if ($stmt instanceof LeanImport)
                $import[] = "$stmt";
            elseif ($stmt instanceof LeanNamespace) {
                $namespace['name'] = "$stmt->namespace";
                if ($namespace['name'] != "$stmt->end")
                    $error['namespace'] = "namespace $stmt->namespace and end $stmt->end do not match";

                foreach ($stmt->statement->args as $stmt) {
                    if ($stmt instanceof LeanTheorem) {
                        if (isset($namespace['theorem']))
                            $error['namespace']['theorem']['name'] = "theorem $namespace[theorem][name] is already defined";
                        elseif ($stmt->assignment instanceof LeanAssign) {
                            $declspec = $stmt->assignment->lhs;
                            if ($declspec instanceof LeanColon) {
                                $attribute = "$stmt->attribute";
                                $imply = "$declspec->rhs";
                                if (preg_match("/^-- imply\n(.+)/s", $imply, $matches))
                                    $imply = $matches[1];

                                [$name, $declspec] = $declspec->lhs->args;

                                $proof = $stmt->assignment->rhs;
                                $typeclass = [];
                                $kwargs = [];
                                $given = null;
                                foreach ($declspec->args as $i => &$stmt) {
                                    if ($stmt instanceof LeanBracket)
                                        $typeclass[] = "$stmt";

                                    elseif ($stmt instanceof LeanBrace)
                                        $kwargs[] = "$stmt";

                                    elseif ($stmt instanceof LeanArgumentsSpaceSeparated) {
                                        if ($stmt->args[0] instanceof LeanBracket)
                                            $typeclass[] = "$stmt";
                                        elseif ($stmt->args[0] instanceof LeanBrace)
                                            $kwargs[] = "$stmt";
                                        else
                                            $error['namespace']['theorem']['Assign'] = "theorem $namespace[theorem][name] is not well-defined";
                                    } elseif ($stmt instanceof LeanLineComment) {
                                        if ($stmt instanceof LeanLineComment && $stmt->arg == 'given') {
                                            $given = array_slice($declspec->args, $i + 1);
                                            $given = implode("\n", array_map(fn($stmt) => "$stmt", $given));
                                            break;
                                        }
                                        if ($kwargs)
                                            $kwargs[] = "$stmt";
                                        else
                                            $typeclass[] = "$stmt";
                                    }
                                }
                                $typeclass = implode("\n", $typeclass);
                                $kwargs = implode("\n", $kwargs);
                                $proof = $proof instanceof LeanBy ?
                                    ['by' => self::merge_proof($proof->arg)] :
                                    self::merge_proof($proof);
                                $namespace['theorem'] = [
                                    'attribute' => $attribute,
                                    'name' => "$name",
                                    'typeclass' => $typeclass,
                                    'kwargs' => $kwargs,
                                    'given' => $given,
                                    'imply' => $imply,
                                    'proof' => $proof
                                ];
                            } else
                                $error['namespace']['theorem']['LeanAssign'] = "$declspec of theorem $namespace[theorem][name] must be of LeanColon Type";
                        } else
                            $error['namespace']['theorem']['Assign'] = "theorem $namespace[theorem][name] is not well-defined";
                    } elseif ($stmt instanceof LeanDef)
                        $namespace['def'][] = "$stmt";
                    elseif ($stmt instanceof LeanLemma)
                        $namespace['lemma'][] = "$stmt";
                }
            } elseif ($stmt instanceof LeanLineComment) {
                if (preg_match('/^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/', "$stmt->arg", $matches))
                    $date[$matches[1]] = $matches[2];
            }
        }

        return [
            'import' => $import,
            'open' => $open,
            'namespace' => $namespace,
            'date' => $date,
            'error' => $error
        ];
    }
}


class LeanImport extends LeanUnary
{
    public function append_dot($caret)
    {
        if ($caret == $this->arg) {
            $new = new LeanCaret($this->indent);
            $this->arg = new LeanDot($this->arg, $new, $this->indent);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0;
            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        return "import $this->arg";
    }

    public function jsonSerialize(): mixed
    {
        return [
            'import' => $this->arg->jsonSerialize()
        ];
    }

    public function append($type)
    {
        if (is_string($type)) {
            $new = new LeanCaret($this->indent);
            $this->sql = new $type($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LeanOpen extends LeanUnary
{
    public function append_dot($caret)
    {
        if ($caret == $this->arg) {
            $new = new LeanCaret($this->indent);
            $this->arg = new LeanDot($this->arg, $new, $this->indent);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0;
            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        return "open $this->arg";
    }

    public function jsonSerialize(): mixed
    {
        return [
            'open' => $this->arg->jsonSerialize()
        ];
    }

    public function append($type)
    {
        if (is_string($type)) {
            $new = new LeanCaret($this->indent);
            $this->sql = new $type($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LeanNamespace extends LeanArgs
{
    public function __construct($namespace, $indent, $parent = null)
    {
        parent::__construct([], $indent, $parent);
        $this->namespace = $namespace;
    }

    public function append_end($caret)
    {
        return $this;
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent <= $indent && $this->statement == null) {
            $this->statement = new LeanCodeBlock([], $this->indent);
            for ($i = 0; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($this->indent);
                $this->statement->push($caret);
            }
            return $caret;
        }
        return parent::append_newline($caret, $newline_count, $indent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -1;
            case "namespace":
                return $this->args[0];
            case "statement":
                return $this->args[1] ?? null;
            case "end":
                return $this->args[2] ?? null;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case "namespace":
                $this->args[0] = $val;
                break;
            case "statement":
                $this->args[1] = $val;
                break;
            case "end":
                $this->args[2] = $val;
                break;

            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function __toString()
    {
        return <<<EOT
namespace $this->namespace
$this->statement
end $this->end
EOT;
    }

    public function jsonSerialize(): mixed
    {
        return [
            'namespace' => $this->namespace->jsonSerialize(),
            'statement' => $this->statement->jsonSerialize(),
            'end' => $this->end->jsonSerialize()
        ];
    }

    public function push_token($word)
    {
        $new = new LeanToken($word, $this->indent);
        $this->end = $new;
        return $new;
    }
}

class LeanBracket extends LeanUnary
{
    public function append_right_bracket()
    {
        return $this;
    }

    public function is_indented()
    {
        $parent = $this->parent;
        if ($parent instanceof LeanSimp || $parent instanceof LeanRw)
            return false;

        if ($parent instanceof LeanArgumentsSpaceSeparated)
            return !std\index($parent->args, $this);

        return true;
    }

    public function __toString()
    {
        $indent = $this->is_indented() ? str_repeat(' ', $this->indent) : '';
        $arg = $this->arg;
        if ($arg instanceof LeanArgumentsCommaNewLineSeparated)
            $arg = "\n$arg\n" . str_repeat(' ', $this->indent);
        return $indent . "[$arg]";
    }

    public function append_simp($caret)
    {
        return $caret->push_token('simp');
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -1;
            default:
                return parent::__get($vname);
        }
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent <= $indent) {
            if ($caret instanceof LeanCaret) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $caret->indent = $indent;
                $this->arg = new LeanArgumentsCommaNewLineSeparated([$caret], $indent);
                return $caret;
            } else {
                if ($indent == $this->indent)
                    return $caret;
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
            }
        } else
            return parent::append_newline($caret, $newline_count, $indent);
    }
}


class LeanBrace extends LeanUnary
{
    public function append_right_brace()
    {
        return $this;
    }

    public function __toString()
    {
        return str_repeat(' ', $this->indent) . "{{$this->arg}}";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -1;
            default:
                return parent::__get($vname);
        }
    }
}


class LeanArrow extends LeanBinary
{
    public function __toString()
    {
        $sep = $this->rhs instanceof LeanCodeBlock ? "\n" : " ";
        return "$this->lhs =>$sep$this->rhs";
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LeanCodeBlock([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::append_newline($caret, $newline_count, $indent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -0.4;
            default:
                return parent::__get($vname);
        }
    }
}

class LeanArrowRight extends LeanBinary
{
    public static $input_precedence = 3.1;
    public function __toString()
    {
        $sep = $this->rhs instanceof LeanCodeBlock ? "\n" : " ";
        return "$this->lhs →$sep$this->rhs";
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LeanCodeBlock([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::append_newline($caret, $newline_count, $indent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -0.4;
            default:
                return parent::__get($vname);
        }
    }
}

class LeanMapsto extends LeanBinary
{
    public function __toString()
    {
        $sep = $this->rhs instanceof LeanCodeBlock ? "\n" : " ";
        return "$this->lhs ↦$sep$this->rhs";
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LeanCodeBlock([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::append_newline($caret, $newline_count, $indent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -0.4;
            default:
                return parent::__get($vname);
        }
    }
}

class LeanArrowLeft extends LeanUnary
{
    public function __toString()
    {
        return "←$this->arg";
    }
}

class LeanNot extends LeanUnary
{
    public function __toString()
    {
        return "¬$this->arg";
    }
}

class LeanMatch extends LeanArgs
{
    public function __construct($subject, $indent, $parent = null)
    {
        parent::__construct([], $indent, $parent);
        $this->subject = $subject;
    }

    public function append_bitor($caret)
    {
        if (count($this->cases) > 0) {
            $cases = $this->cases;
            $caret = end($cases);
            if ($caret instanceof LeanCaret)
                return $caret;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent > $indent)
            return parent::append_newline($caret, $newline_count, $indent);

        $cases = $this->cases;
        if (count($cases) > 0) {
            $caret = end($cases);
            if ($caret instanceof LeanCaret)
                return $caret;

            if ($caret instanceof LeanArrow) {
                $caret = new LeanCaret($this->indent);
                $this->push($caret);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_with($caret)
    {
        if (!$this->cases) {
            $new = new LeanCaret($this->indent);
            $this->push($new);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function __toString()
    {
        $indent = str_repeat(' ', $this->indent);
        $cases = $this->cases;
        $cases = array_map(fn($args) => "$indent| $args", $cases);
        $cases = implode("\n", $cases);
        return "{$indent}match $this->subject with\n$cases";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -0.4;
            case "subject":
                return $this->args[0];
            case "cases":
                return array_slice($this->args, 1);
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case "subject":
                $this->args[0] = $val;
                break;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }
}

class LeanArgumentsSpaceSeparated extends LeanArgs
{
    public function __toString()
    {
        $indent = $this->parent instanceof LeanCodeBlock? str_repeat(' ', $this->indent) : '';
        return $indent . implode(" ", array_map(fn($arg) => "$arg", $this->args));
    }
}

class LeanArgumentsNewLineSeparated extends LeanArgs
{
    public function __toString()
    {
        return implode("\n", array_map(fn($arg) => "$arg", $this->args));
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent > $indent)
            return parent::append_newline($caret, $newline_count, $indent);

        if ($this->indent < $indent) {
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } else {
            if (end($this->args) === $caret) {
                for ($i = 0; $i < $newline_count; ++$i) {
                    $caret = new LeanCaret($indent);
                    $this->push($caret);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }
}

class LeanArgumentsCommaSeparated extends LeanArgs
{
    public function __toString()
    {
        return implode(", ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -1;
            default:
                return parent::__get($vname);
        }
    }

    public function append_comma($caret)
    {
        $caret = new LeanCaret($this->indent);
        $this->push($caret);
        return $caret;
    }
}

class LeanArgumentsCommaNewLineSeparated extends LeanArgs
{
    public function __toString()
    {
        return implode(",\n", array_map(fn($arg) => "$arg", $this->args));
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent > $indent)
            return parent::append_newline($caret, $newline_count, $indent);

        if ($this->indent < $indent) {
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } else {
            if (end($this->args) === $caret) {
                for ($i = 0; $i < $newline_count - 1; ++$i) {
                    $caret = new LeanCaret($indent);
                    $this->push($caret);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -1;
            default:
                return parent::__get($vname);
        }
    }

    public function append_comma($caret)
    {
        $caret = new LeanCaret($this->indent);
        $this->push($caret);
        return $caret;
    }
}


trait LeanTactic
{
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0;
            default:
                return parent::__get($vname);
        }
    }
}

class LeanBy extends LeanUnary
{
    use LeanTactic;
    public function __toString()
    {
        $sep = $this->arg instanceof LeanCodeBlock ? "\n" : ' ';
        return "by$sep$this->arg";
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanCodeBlock([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::append_newline($caret, $newline_count, $indent);
    }

    public function jsonSerialize(): mixed
    {
        return [
            'by' => $this->arg->jsonSerialize()
        ];
    }
}


class LeanCase extends LeanUnary
{
    use LeanTactic;
    public function __toString()
    {
        return str_repeat(' ', $this->indent) . "case $this->arg";
    }

    public function jsonSerialize(): mixed
    {
        return [
            'case' => $this->arg->jsonSerialize()
        ];
    }
}

class LeanCases extends LeanUnary
{
    use LeanTactic;
    public function __toString()
    {
        return str_repeat(' ', $this->indent) . "cases $this->arg";
    }
    public function jsonSerialize(): mixed
    {
        return [
            'cases' => $this->arg->jsonSerialize()
        ];
    }
}

class LeanByContra extends LeanUnary
{
    use LeanTactic;
    public function __toString()
    {
        return str_repeat(' ', $this->indent) . "by_contra $this->arg";
    }

    public function jsonSerialize(): mixed
    {
        return [
            'by_contra' => $this->arg->jsonSerialize()
        ];
    }
}

trait LeanTacticModifier
{
    public function __construct($rule, $indent, $parent = null)
    {
        parent::__construct([], $indent, $parent);
        $this->rule = $rule;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0;
            case "rule":
                return $this->args[0];

            case "at":
                return $this->args[1] ?? null;

            default:
                return parent::__get($vname);
        }
    }
    public function __set($vname, $val)
    {
        switch ($vname) {
            case "rule":
                $this->args[0] = $val;
                break;

            case "at":
                $this->args[1] = $val;
                break;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }
    public function __toString()
    {
        $indent = str_repeat(' ', $this->indent);
        $name = $this->tactic_name();
        $name = "{$indent}$name";
        $at = $this->at;
        if ($at)
            $at = " at $at";
        else
            $at = "";

        $rule = $this->rule;
        if ($rule) {
            if ($rule instanceof LeanCaret)
                $rule = "";
            else {
                $rule = " $rule";
            }
        } else
            $rule = "";

        return "$name$rule$at";
    }

    public function append_at($rule)
    {
        if ($this->at === null) {
            if ($rule === $this->rule) {
                $new = new LeanCaret($this->indent);
                $this->at = $new;
                return $new;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function jsonSerialize(): mixed
    {
        $json = [
            $this->tactic_name() => $this->rule->jsonSerialize()
        ];
        if ($this->at)
            $json['at'] = $this->at->jsonSerialize();
        return $json;
    }
}

class LeanRw extends LeanArgs
{
    use LeanTacticModifier;

    public function tactic_name()
    {
        return 'rw';
    }
    public function jsonSerialize(): mixed
    {
        $json = [
            'rw' => $this->rule->jsonSerialize()
        ];
        if ($this->at)
            $json['at'] = $this->at->jsonSerialize();
        return $json;
    }
}

class LeanSimp extends LeanArgs
{
    private $only = false;
    use LeanTacticModifier;
    public function tactic_name()
    {
        if ($this->only)
            return 'simp only';
        return 'simp';
    }

    public function jsonSerialize(): mixed
    {
        $json = [
            'simp' => $this->rule->jsonSerialize()
        ];
        if ($this->at)
            $json['at'] = $this->at->jsonSerialize();
        if ($this->only)
            $json['only'] = true;
        return $json;
    }
}


class LeanAttribute extends LeanUnary
{
    public function __toString()
    {
        return "@$this->arg";
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        return $caret;
    }

    public function append($new)
    {
        switch ($new) {
            case 'LeanTheorem':
            case 'LeanLemma':
            case 'LeanDef':
                $caret = new LeanCaret($this->indent);
                $new = new $new($caret, $this->indent);
                $this->parent->replace($this, $new);
                $new->attribute = $this;
                return $caret;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        // return $this->parent->append($new);
    }
}


class LeanDef extends LeanArgs
{
    public function __construct($name, $indent, $parent = null)
    {
        parent::__construct([$name], $indent, $parent);
        array_unshift($this->args, null);
    }

    public function __toString()
    {
        $def = "$this->func $this->assignment";
        if ($this->attribute)
            $def = "$this->attribute\n$def";
        return $def;
    }

    public function jsonSerialize(): mixed
    {
        $json = [
            $this->func => parent::jsonSerialize()
        ];
        if ($this->attribute)
            $json['attribute'] = $this->attribute->jsonSerialize();
        return $json;
    }

    public function append_newline($caret, $newline_count, $indent)
    {
        if ($this->indent < $indent) {
            if ($caret === $this->assignment) {
                if ($caret instanceof LeanToken) {
                    $new = new LeanCaret($indent);
                    $this->assignment = new LeanArgumentsNewLineSeparated(
                        [
                            $this->assignment,
                            new LeanArgumentsNewLineSeparated([$new], $indent)
                        ],
                        $this->indent
                    );
                    return $new;
                }
                if ($caret instanceof LeanColon) {
                    if ($caret->rhs instanceof LeanCaret) {
                        $caret = $caret->rhs;
                        $caret->indent = $indent;
                        $this->assignment->rhs = new LeanCodeBlock([$caret], $indent);
                        return $caret;
                    }
                }
                elseif ($caret instanceof LeanAssign) {
                    $caret = $this->assignment->rhs;
                    $caret->indent = $indent;
                    $this->assignment->rhs = new LeanCodeBlock([$caret], $indent);
                    return $caret;
                }
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        return parent::append_newline($caret, $newline_count, $indent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return -2;
            case "attribute":
                return $this->args[0] ?? null;
            case "assignment":
                return $this->args[1] ?? null;
            case "func":
                return 'def';
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case "attribute":
                $this->args[0] = $val;
                break;
            case "assignment":
                $this->args[1] = $val;
                break;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function append_simp($caret)
    {
        return $caret->push_token('simp');
    }
}


class LeanTheorem extends LeanDef
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'theorem';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanLemma extends LeanDef
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'lemma';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanQuantifier extends LeanArgs
{
    public function __construct($bound, $indent, $parent = null)
    {
        parent::__construct([$bound], $indent, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "bound":
                // bound variable or quantified variable.
                return $this->args[0];
            case "scope":
                // body or scope of the quantifier.
                return $this->args[1]?? null;

            case "stack_precedence":
                return 0.1;
        
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case "bound":
                $this->args[0] = $val;
                break;
            case "scope":
                $this->args[1] = $val;
                break;

            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }
    
    public function __toString()
    {
        return "$this->func $this->bound, $this->scope";
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => parent::jsonSerialize()
        ];
    }

    public function append_comma($caret)
    {
        if ($caret === $this->bound) {
            $caret = new LeanCaret($this->indent);
            $this->scope = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}


// universal quantifier
class LeanForall extends LeanQuantifier
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return '∀';
    
            default:
                return parent::__get($vname);
        }
    }

}

// existential quantifier
class LeanExists extends LeanQuantifier
{
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return '∃';
    
            default:
                return parent::__get($vname);
        }
    }
}


function compile($code)
{
    $caret = new LeanCaret(0);
    $root = new LeanModule([$caret], 0);
    $tokens = array_map(fn($args) => $args[0][0], std\matchAll('/\w+|\W/u', $code));
    $i = 0;
    $count = count($tokens);
    while ($i < $count) {
        $token = $tokens[$i];
        switch ($token) {
            case 'import':
            case 'open':
            case 'namespace':
            case 'def':
            case 'theorem':
            case 'lemma':
            case 'match':
                $Type = std\capitalize($token);
                $caret = $caret->append("Lean$Type");
                break;

            case ' ':
                $caret = $caret->parent->append_space($caret);
                break;

            case "\t":
                throw new Exception("Tab is not allowed in Lean");
            case "\r":
                throw new Exception("Carriage return is not allowed in Lean");

            case "\n":
                $indent = $j = 0;
                $newline_count = 1;
                while (true) {
                    while ($tokens[$i + ++$j] == ' ')
                        ++$indent;
                    if ($tokens[$i + $j] == "\n") {
                        ++$newline_count;
                        $indent = 0;
                    } else
                        break;
                }
                if ($i + $j + 1 < $count && $tokens[$i + $j] == '-' && $tokens[$i + $j + 1] == '-') {
                    $indent = $caret->indent;
                    if (
                        $caret instanceof LeanCaret &&
                        ($caret->parent instanceof LeanColon || $caret->parent instanceof LeanBy || $caret->parent instanceof LeanAssign)
                    )
                        $indent += 2;
                } elseif ($indent == 0 && $i + $j < $count && $tokens[$i + $j] == 'end')
                    // end of namespace
                    $newline_count -= 1;
                $caret = $caret->parent->append_newline($caret, $newline_count, $indent);
                $i += $j - 1;
                break;

            case '.':
                $caret = $caret->append_binary("LeanDot");
                break;

            case 'is':
                $Type = std\capitalize($token);
                $Type = "Lean$Type";
                $not = $i + 2 < $count && std\isspace($tokens[$i + 1]) && strtolower($tokens[$i + 2]) == 'not';
                if ($not) {
                    $Type .= 'Not';
                    $i += 2;
                }

                $caret = $caret->append_binary($Type);
                break;

            case '(':
                $caret = $caret->parent->append_left_parenthesis($caret);
                break;

            case ')':
                $caret = $caret->parent->append_right_parenthesis();
                break;

            case '[':
                $caret = $caret->parent->append_left_bracket($caret);
                break;

            case ']':
                $caret = $caret->parent->append_right_bracket();
                break;

            case '{':
                $caret = $caret->parent->append_left_brace($caret);
                break;

            case '}':
                $caret = $caret->parent->append_right_brace();
                break;

            case '⟨':
                $caret = $caret->parent->append_left_angle_bracket($caret);
                break;
            case '⟩':
                $caret = $caret->parent->append_right_angle_bracket();
                break;

            case '\\':
                $word = "\\" . $tokens[$i + 1];
                $caret = $caret->push_token($word);
                ++$i;
                break;

            case '<':
                if ($i + 1 < $count && $tokens[$i + 1] == '=') {
                    $caret = $caret->append_binary('LeanLe');
                    ++$i;
                } else
                    $caret = $caret->append_binary('LeanLt');
                break;

            case '>':
                if ($i + 1 < $count && $tokens[$i + 1] == '=') {
                    $caret = $caret->append_binary('LeanGe');
                    ++$i;
                } else
                    $caret = $caret->append_binary('LeanGt');
                break;

            case '≤':
                $caret = $caret->append_binary('LeanLe');
                break;

            case '≥':
                $caret = $caret->append_binary('LeanGe');
                break;

            case '=':
                if ($i + 1 < $count && $tokens[$i + 1] == '>') {
                    $caret = $caret->append_binary('LeanArrow');
                    ++$i;
                } else
                    $caret = $caret->append_binary('LeanEq');
                break;

            case '!':
                if ($i + 1 < $count && $tokens[$i + 1] == '=') {
                    $caret = $caret->append_binary('LeanNe');
                    ++$i;
                } else
                    throw new Exception("Unexpected token $token");
                break;

            case '≠':
                $caret = $caret->append_binary('LeanNe');
                break;

            case ',':
                $caret = $caret->parent->append_comma($caret);
                break;

            case ':':
                if ($i + 1 < $count && $tokens[$i + 1] == '=') {
                    ++$i;
                    $caret = $caret->parent->append_assign($caret);
                } else
                    $caret = $caret->parent->append_colon($caret);
                break;

            case ';':
                $caret = $caret->parent->append_semicolon();
                break;

            case '-':
                if ($i + 1 < $count && $tokens[$i + 1] == '-') {
                    ++$i;
                    $comment = "";
                    while ($tokens[++$i] != "\n")
                        $comment .= $tokens[$i];
                    $caret = $caret->append_line_comment(trim($comment));
                } else
                    $caret = $caret->append_arithmetic($token);
                break;

            case '*':
                $caret = $caret->append_arithmetic($token);
                break;

            case '|':
                if ($i + 1 < $count && $tokens[$i + 1] == '|') {
                    $caret = $caret->parent->append_arithmetic('||');
                    ++$i;
                } else
                    $caret = $caret->parent->append_bitor($caret);
                break;

            case '&':
                if ($i + 1 < $count && $tokens[$i + 1] == '&') {
                    $caret = $caret->parent->append_arithmetic('&&');
                    ++$i;
                } else
                    $caret = $caret->parent->append_bitand($caret);
                break;

            case "'":
                $caret = $caret->append_quote();
                break;

            case '+':
            case '/':
            case '%':
            case '^':
            case '<<':
            case '>>':
            case '×':
            case '•':
            case '⊙':
            case '⊗':
            case '⊕':
            case '⊖':
            case '⊘':
            case '⊚':
            case '⊛':
            case '⊜':
            case '⊝':
            case '⊞':
            case '⊟':
            case '⊠':
                $caret = $caret->append_arithmetic($token);
                break;
            
            case '←':
                $caret = $caret->append_unary('LeanArrowLeft');
                break;

            case '→':
                $caret = $caret->append_binary('LeanArrowRight');
                break;

            case '↦':
                $caret = $caret->append_binary('LeanMapsto');
                break;

            case '↔':
                $caret = $caret->append_binary('LeanIff');
                break;

            case '∀':
                $caret = $caret->append('LeanForall');
                break;

            case '∃':
                $caret = $caret->append('LeanExists');
                break;
            
            case '∧':
                $caret = $caret->append_binary('LeanAnd');
                break;

            case '∨':
                $caret = $caret->append_binary('LeanOr');
                break;

            case '¬':
                $caret = $caret->append_unary('LeanNot');
                break;

            case 'with':
                $caret = $caret->parent->append_with($caret);
                break;

            case 'by':
                $caret = $caret->parent->append_by($caret);
                break;

            case 'cases':
                $caret = $caret->parent->append_cases($caret);
                break;

            case 'case':
                $caret = $caret->parent->append_case($caret);
                break;

            case 'by_contra':
                $caret = $caret->parent->append_by_contra($caret);
                break;

            case 'rw':
                $caret = $caret->parent->append_rw($caret);
                break;

            case 'simp':
                $caret = $caret->parent->append_simp($caret);
                break;

            case 'at':
                $caret = $caret->parent->append_at($caret);
                break;

            case 'end':
                $caret = $caret->parent->append_end($caret);
                break;

            case '@':
                $caret = $caret->append_unary('LeanAttribute');
                break;

            default:
                $caret = $caret->parent->append_token($caret, $token);
        }
        ++$i;
    }

    return $root;
}
