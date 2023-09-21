<?php
require_once dirname(__file__).'/../std.php';

abstract class SQL implements JsonSerializable
{

    public $parent;

    public function remove_negation() {
        return false;    
    }

    public function delete() {
        $this->parent->removeChild($this);
    }
    
    public function append_from()
    {
        return $this->parent->append_from();
    }
    
    public function append_where()
    {
        return $this->parent->append_where();
    }
    
    public function append_order()
    {
        return $this->parent->append_order();
    }
    
    public function append_group()
    {
        return $this->parent->append_group();
    }
    
    public function append_having()
    {
        return $this->parent->append_having();
    }
    
    public function append_limit()
    {
        return $this->parent->append_limit();
    }
    
    public function append_offset()
    {
        return $this->parent->append_offset();
    }
    
    public function append_space()
    {
        return $this;
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
        if ($type::$input_precedence > $parent->stack_precedence){
            $new = new SQLCaret();
            $parent->replace($this, new $type($this, $new));
            return $new;
        }
        else {
            return $this->parent->append_binary($type);
        }
    }
    
    public function append_or()
    {
        $parent = $this->parent;
        return SQLOr::$input_precedence > $parent->stack_precedence ? $this->append_multiple("SQLOr", new SQLCaret()) : $parent->append_or();
    }

    public function append_multiple($Type, $caret)
    {
        $parent = $this->parent;
        if ($parent instanceof $Type) {
            $parent->args[] = $caret;
            $caret->parent = $parent;
        } else {
            $parent->replace($this, new $Type([$this,$caret], $parent));
        }

        return $caret;
    }

    public function append_token(&$word)
    {
        return $this->append(new SQLToken($word));
    }

    public function append_comma()
    {
        return $this->parent->append_comma();
    }
    
    public function append_unary($Type)
    {
        $caret = new SQLCaret();
        $this->append(new $Type($caret));
        return $caret;
    }

    public function __construct($parent = null)
    {
        $this->parent = $parent;
    }

    public function append_right_bracket()
    {
        $caret = $this;
        $old = $this;
        for (;;) {
            if ($caret === null) {
                error_log("unnecessary right bracket at position detected");
                break;
            }
            $old = $caret;
            $caret = $caret->parent;
            if ($caret instanceof SQLCharProperty) {
                break;
            }
        }
        if ($caret === null) {
            $caret = $old;
        }

        return $caret;
    }

    public function append_right_parenthesis()
    {
        return $this->parent->append_right_parenthesis();
    }

    static public function compile($sql, $transform_fn=true)
    {
        $caret = new SQLCaret();
        $root = new SQLSentence($caret);
        $matches = std\matchAll('/\w+|\W/u', $sql);
        $i = 0;
        $count = count($matches);
        while ($i < $count) {
            [[$token]] = $matches[$i];
            switch ($token) {
                case 'select':
                    $caret = $caret->append('SQLSelect');
                    break;
                    
                case ' ':
                case '\t':
                    $caret = $caret->append_space();
                    break;
                    
                case '.':
                    $caret = $caret->append_dot();
                    break;
                    
                case 'group':
                case 'order':
                    $j = 1;
                    while ($i + $j < $count && $matches[$i + $j][0][0] == ' ') {
                        ++$j;
                    }
                    
                    if ($i + $j < $count && $matches[$i + $j][0][0] == 'by') {
                        $func = "append_$token";
                        $caret = $caret->parent->$func();
                        
                        $i += $j;
                        break;
                    }
                    
                    $caret = $caret->append_token($token);
                    break;
                    
                case 'from':
                case 'where':
                case 'limit':
                case 'offset':
                case 'having':
                    $func = "append_$token";
                    $caret = $caret->parent->$func();
                    break;

                case '-':
                    if ($i + 1 < $count && $matches[$i + 1][0][0] == '>') {
                        $caret = $caret->append_binary('SQLArrow');
                        ++$i;
                        break;
                    }

                    $caret = $caret->append_minus();
                    break;
                    
                case "'":
                    $caret = $caret->append('SQLQuote');
                    break;
                    
                case 'regexp':
                case 'and':
                case 'or':
                case 'as':
                case 'join':
                case 'in':
                    $Type = std\capitalize($token);
                    $caret = $caret->append_binary("SQL$Type");
                    break;
                    
                case '(':
                    $caret = $caret->append_left_parenthesis();
                    break;

                case ')':
                    $caret = $caret->parent->append_right_parenthesis();
                    break;

                case '\\':
                    $word = "\\" . $matches[$i + 1];
                    $caret = $caret->append_token($word);
                    ++ $i;
                    break;

                case '<':
                    if ($i + 1 < $count && $matches[$i + 1][0][0] == '=') {
                        $caret = $caret->append_binary('SQLLe');
                        ++$i;
                        break;
                    }
                    
                    $caret = $caret->append_binary('SQLLt');
                    break;
                    
                case '>':
                    if ($i + 1 < $count && $matches[$i + 1][0][0] == '=') {
                        $caret = $caret->append_binary('SQLGe');
                        ++$i;
                        break;
                    }
                    
                    $caret = $caret->append_binary('SQLGt');
                    break;
                    
                case '=':
                    $caret = $caret->append_binary('SQLEq');
                    break;

                case '!':
                    if ($i + 1 < $count && $matches[$i + 1][0][0] == '=') {
                        $caret = $caret->append_binary('SQLNe');
                        ++$i;
                        break;
                    }
                    $caret = $caret->append_token($token);
                    break;
                    
                case 'with':
                    $caret = $caret->append_with();
                    break;

                case ',':
                    $caret = $caret->parent->append_comma();
                    break;

                case 'inner':
                case 'cross':
                case 'left':
                case 'right':
                case 'full':
                    $j = 1;
                    while ($i + $j < $count && $matches[$i + $j][0][0] == ' ') {
                        ++$j;
                    }
                    
                    if ($i + $j < $count && $matches[$i + $j][0][0] == 'join') {
                        $Type = std\capitalize($token);
                        $caret = $caret->append_binary("SQL${Type}Join");
                        $i += $j;
                        break;
                    }
                    $caret = $caret->append_token($token);
                    break;
                    
                case 'path':
                case 'distinct':
                case 'separator':
                    $caret = $caret->parent->append_operator($token);
                    break;
                    
                case 'delete':
                    $caret = $caret->append('SQLDelete');
                    break;
                    
                default:
                    $caret = $caret->append_token($token);
            }
            ++$i;
        }

        return $root;
    }
}

class SQLCaret extends SQL
{

    public function __toString()
    {
        return "";
    }

    public function append($new)
    {
        if (is_string($new)) {
            $this->parent->replace($this, new $new($this));
            return $this;
        }
        else {
            $this->parent->replace($this, $new);
            return $new;
        }
    }
    
    public function append_with()
    {
        $this->parent->replace($this, new SQLWith($this, null));
        return $this;
    }
    
    public function jsonSerialize()
    {
        return "";
    }
    
    public function append_left_parenthesis()
    {
        $this->parent->replace($this, new SQLGroup($this));
        return $this;
    }
}

class SQLToken extends SQL
{

    public $arg;

    public function __construct($arg, $parent = null)
    {
        parent::__construct($parent);
        $this->arg = $arg;
    }

    public function __toString()
    {
        return $this->arg;
    }

    public function append_token(&$word)
    {
        if (std\fullmatch("/\w+/", $this->arg) && std\fullmatch("/\w+/", $word)) {
            $new = new SQLToken($word);
            $this->parent->replace($this, new SQLParallelArgs([$this, $new]));
            return $new;
        }
        
        $this->arg .= $word;
        return $this;
    }

    public function append_left_parenthesis()
    {
        $new = new SQLCaret();
        $this->parent->replace($this, new SQLFunction($this, $new));
        return $new;
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "length":
                return count($this->chars());
        }
    }

    public function append_dot()
    {
        $parent = $this->parent;
        if ($parent instanceof SQLStatement && $this === $parent->from) {
            $caret = new SQLCaret();
            $parent->replace($this, new SQLDot($this, $caret));
            return $caret;
        } else {
            $this->arg .= '.';
            return $this;
        }
    }

    public function append($new)
    {
        return $this->parent->append($new);
    }
    
    public function jsonSerialize()
    {
        return $this->arg;
    }
}

class SQLUnary extends SQL
{
    public static $input_precedence = 2;
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 2;
        }
    }
    
    public $arg;

    public function __construct($arg, $parent = null)
    {
        parent::__construct($parent);
        $this->arg = $arg;
        $arg->parent = $this;
    }

    public function replace($old, $new)
    {
        $this->arg = $new;
        if (!$new->parent)
            $new->parent = $this;
    }

    public function __clone()
    {
        parent::__clone();
        $this->arg = clone $this->arg;
        $this->arg->parent = $this;
    }
    
    public function jsonSerialize()
    {
        return $this->arg->jsonSerialize();
    }
}

class SQLQuote extends SQLUnary
{
    public function __construct($arg, $parent = null)
    {
        parent::__construct($arg, $parent);
    }

    public function __toString()
    {
        return "'$this->arg'";
    }
    
    public function append($new)
    {
        if ($new == 'SQLQuote')
            return $this;
        
        if ($new instanceof SQLToken) {
            $this->parent->replace($this, new SQLParallelArgs([$this, $new]));
            return $new;
        }
        
        throw new Exception('public function append($new)');
    }
}

class SQLOperator extends SQLUnary
{
    public $func;
    public function __construct($func, $arg, $parent = null)
    {
        parent::__construct($arg, $parent);
        $this->func = $func;
    }
    
    public function __toString()
    {
        return "$this->func $this->arg";
    }
    
    public function jsonSerialize()
    {
        $func = $this->func;
        switch ($this->func) {
            case 'order by':
                $func = 'order';
        }
        return [$func => $this->arg->jsonSerialize()];
    }
}

class SQLGroup extends SQLUnary
{
    public function __construct($arg, $parent = null)
    {
        parent::__construct($arg, $parent);
    }
    
    public function __toString()
    {
        return "($this->arg)";
    }
    
    public function append_right_parenthesis()
    {
        return $this;
    }
}

abstract class SQLArgs extends SQL
{
    public static $input_precedence = 2;
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 2;
        }
    }
    
    public $args;

    public function __construct($args, $parent = null)
    {
        parent::__construct($parent);
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }
    }

    public function replace($old, $new)
    {
        $i = std\indexOf($this->args, $old);
        if ($i < 0) {
            throw new Exception("replace(old, replacement)");
        }

        if (is_array($new)) {
            array_splice($this->args, $i, 1, $new);
            foreach ($new as $el) {
                if (!$el->parent)
                    $el->parent = $this;
            }
        }
        else {
            $this->args[$i] = $new;
            if (!$new->parent)
                $new->parent = $this;
        }
    }

    public function removeChild($node) {
        $i = std\indexOf($this->args, $node);
        if ($i < 0)
            throw new Exception("removeChild(\$node)");
        std\array_delete($this->args, $i);
        
        if (count($this->args) == 1) {
            [$arg] = $this->args;
            $parent = $this->parent;
            $parent->replace($this, $arg);
            $arg->parent = $parent;
        }
    }
    
    public function jsonSerialize()
    {
        return array_map(fn ($arg) => $arg->jsonSerialize(), $this->args);
    }
}

class SQLBinary extends SQLArgs
{
    public static $input_precedence = 2;

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct([$lhs, $rhs], $parent);
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
        }
    }
    
    public function jsonSerialize()
    {
        return [$this->func => [$this->lhs->jsonSerialize(), $this->rhs->jsonSerialize()]];
    }
}

class SQLDot extends SQLBinary
{
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(".", array_map(fn ($arg) => "$arg", $this->args));
    }
 
    public function jsonSerialize()
    {
        return [$this->lhs->jsonSerialize() => $this->rhs->jsonSerialize()];
    }
}

class SQLRegexp extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" regexp ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'regexp';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLGt extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" > ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'gt';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLGe extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" >= ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'ge';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLLt extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" < ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'lt';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLLe extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" <= ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'le';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLEq extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" = ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'eq';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLNe extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" != ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'ne';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLAs extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" as ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'as';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLIn extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" in ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'in';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLInnerJoin extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" join ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'join';
            default:
                return parent::__get($vname);
        }
    }
}

define("SQLInnerJoin", "SQLJoin");

class SQLCrossJoin extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" cross join ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'cross_join';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLLeftJoin extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" left join ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'left_join';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLRightJoin extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" right join ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'right_join';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLFullJoin extends SQLBinary
{
    public static $input_precedence = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" full join ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "func":
                return 'full_join';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLArrow extends SQLBinary
{
    public static $input_precedence = 5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode("->", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 4;
            case "func":
                return 'json_extract';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLAnd extends SQLBinary
{
    public static $input_precedence = 2;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" and ", array_map(fn ($arg) => "$arg", $this->args));
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
    
    public function jsonSerialize()
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof SQLAnd) {
            return ['and' => [...$lhs['and'], $rhs]];
        }

        return ['and' => [$lhs, $rhs]];
    }
}

class SQLOr extends SQLBinary
{
    public static $input_precedence = 2;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }
    
    public function __toString()
    {
        return implode(" or ", array_map(fn ($arg) => "$arg", $this->args));
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 4;
            default:
                return parent::__get($vname);
        }
    }
    
    public function jsonSerialize()
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof SQLOr) {
            return ['or' => [...$lhs['or'], $rhs]];
        }
        
        return ['or' => [$lhs, $rhs]];
    }
}

class SQLFunction extends SQLArgs
{
    public function __construct($func, ...$args)
    {
        parent::__construct([$func, ...$args]);
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 3;
            case "func":
                return $this->args[0];
            case "parameters":
                return array_slice($this->args, 1);
        }
    }

    public function __toString()
    {
        $args = implode(", ", array_map(fn ($arg) => "$arg", $this->parameters));
        return "$this->func($args)";
    }
    
    public function jsonSerialize()
    {
        $parameters = $this->parameters;
        if (count($parameters) == 1 && $parameters[0] instanceof SQLCaret) {
            $parameters = [];
        }
        return ["$this->func" => array_map(fn ($arg) => $arg->jsonSerialize(), $parameters)];
    }
    
    public function append_comma()
    {
        $new = new SQLCaret($this);
        $this->args[] = $new;
        return $new;
    }
    
    public function append_right_parenthesis()
    {
        return $this;
    }
    
    public function append_order()
    {
        $new = new SQLCaret();
        $index = count($this->args) - 1;
        $this->args[$index] = new SQLParallelArgs([$this->args[$index], new SQLOperator('order by', $new)], $this);
        return $new;
    }
}

class SQLParallelArgs extends SQLArgs
{
    public static $input_precedence = 2;
    
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 2;
        }
    }
    
    public function append($new)
    {
        if ($new instanceof SQLToken) {
            $this->args[] = $new;
            $new->parent = $this;
            return $new;
        }
        
        throw new Exception('public function append($type)');
    }
    
    public function __toString()
    {
        return implode(" ", array_map(fn ($arg) => "$arg", $this->args));
    }

    public function append_operator($func)
    {
        $new = new SQLCaret();
        $this->args[] = new SQLOperator($func, $new, $this);
        return $new;
    }    
}

class SQLSentence extends SQLUnary
{

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0;
        }
    }

    public function __toString()
    {
        return "$this->arg";
    }

    public function is_possibly_empty()
    {
        return $this->arg->is_possibly_empty();
    }
    
    public function is_or_structure()
    {
        return $this->arg->is_or_structure();
    }
    
}

class SQLStatement extends SQL
{
    public $from;
    public $where;
    public $group;
    public $having;
    public $order;
    public $limit;
    public $offset;

    public function __construct($from = null, $where = null, $group = null, $having = null, $order = null, $limit = null, $offset = null, $parent = null)
    {
        parent::__construct($parent);
        $this->from = $from;
        $this->where = $where;
        $this->group = $group;
        $this->having = $having;
        $this->order = $order;
        $this->limit = $limit;
        $this->offset = $offset;
        
        $from->parent = $this;
        $where->parent = $this;

        if ($group)
            $group->parent = $this;
        if ($having)
            $having->parent = $this;
        
        if ($order)
            $order->parent = $this;
        if ($limit)
            $limit->parent = $this;
        if ($offset)
            $offset->parent = $this;
    }
    
    public function replace($old, $new)
    {
        if ($this->from === $old) {
            $this->from = $new;
        }
        elseif ($this->where === $old) {
            $this->where = $new;
        }
        elseif ($this->order === $old) {
            $this->order = $new;
        }
        elseif ($this->limit === $old) {
            $this->limit = $new;
        }
        elseif ($this->offset === $old) {
            $this->offset = $new;
        }
        elseif ($this->group === $old){
            $this->group = $new;
        }
        elseif ($this->having === $old){
            $this->having = $new;
        }
        else {
            throw new Exception('public function replace($old, $new)');
        }

        if (!$new->parent)
            $new->parent = $this;
    }
    
    public function jsonSerialize()
    {
        return [
            'where' => $this->where? $this->where->jsonSerialize(): null,
            'from' => $this->from->jsonSerialize(),
            'group' => $this->group? $this->group->jsonSerialize(): null,
            'having' => $this->having? $this->having->jsonSerialize(): null,
            'order' => $this->order? $this->order->jsonSerialize(): null,
            'limit' => $this->limit? $this->limit->jsonSerialize(): null,
            'offset' => $this->offset? $this->offset->jsonSerialize(): null,
        ];
    }
}

class SQLSelect extends SQLStatement
{
    public $select;
    public function __construct($select, $from = null, $where = null, $group = null, $having = null, $order = null, $limit = null, $offset = null, $parent = null)
    {
        parent::__construct($from, $where, $group, $having, $order, $limit, $offset, $parent);
        $this->select = $select;
        $select->parent = $this;
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0;
        }
    }
    
    public function append_from()
    {
        if (!$this->from) {
            $this->from = new SQLCaret($this);
            return $this->from;
        }
        
        throw new Exception('public function append_from()');
    }
    
    public function append_where()
    {
        if (!$this->where) {
            $this->where = new SQLCaret($this);
            return $this->where;
        }
        
        throw new Exception('public function append_where()');
    }

    public function append_group()
    {
        if (!$this->group) {
            $this->group = new SQLCaret($this);
            return $this->group;
        }
        
        throw new Exception('public function append_group()');
    }
    
    public function append_having()
    {
        if (!$this->having) {
            $this->having = new SQLCaret($this);
            return $this->having;
        }
        
        throw new Exception('public function append_having()');
    }
    
    public function append_order()
    {
        if (!$this->order) {
            $this->order = new SQLCaret($this);
            return $this->order;
        }
        
        throw new Exception('public function append_order()');
    }
    
    public function append_limit()
    {
        if (!$this->limit) {
            $this->limit = new SQLCaret($this);
            return $this->limit;
        }
        
        throw new Exception('public function append_limit()');
    }
    
    public function append_offset()
    {
        if (!$this->offset) {
            $this->offset = new SQLCaret($this);
            return $this->offset;
        }
        
        throw new Exception('public function append_offset()');
    }
    
    public function __toString()
    {
        if (std\is_list($this->select)) {
            $select = implode(', ', array_map(fn ($arg) => "$arg", $this->select));
        }
        else {
            $select = $this->select;
        }

        $sql = "select $select from $this->from";
        $where = $this->where;
        if ($where) {
            $sql .= " where $where";
        }
        
        $group = $this->group;
        if ($group) {
            $sql .= " group by $group";
            $having = $this->having;
            if ($having) {
                $sql .= " having $having";
            }
        }
        
        $order = $this->order;
        if ($order) {
            $sql .= " order by $order";
        }
        
        $limit = $this->limit;
        if ($limit) {
            $sql .= " limit $limit";
            
            $offset = $this->offset;
            if ($offset) {
                $sql .= " offset $offset";
            }
        }
        
        return $sql;
    }
    
    public function replace($old, $new)
    {
        if (std\is_list($this->select)) {
            $i = std\indexOf($this->select, $old);
            if ($i >= 0) {
                $this->select[$i] = $new;
                if (!$new->parent)
                    $new->parent = $this;
                    return;
            }
        }
        elseif ($this->select === $old) {
            $this->select = $new;
            if (!$new->parent)
                $new->parent = $this;
            
            return;
        }

        parent::replace($old, $new);
    }
    
    public function jsonSerialize()
    {
        $dict = parent::jsonSerialize();
        if (std\is_list($this->select)) {
            $dict['select'] = array_map(fn ($arg) => $arg->jsonSerialize(), $this->select);
        }
        else {
            $dict['select'] = $this->select->jsonSerialize();
        }
        
        return $dict;
    }
    
    public function append_comma()
    {
        if (!$this->from) {
            $new = new SQLCaret($this);
            if (std\is_list($this->select)) {
                $this->select[] = $new;
            }
            else {
                $this->select = [$this->select, $new];
            }
            return $new;
        }
    }
    
    public function append_operator($func)
    {
        assert($func == "distinct", '$func == "distinct"');
        if ($this->select instanceof SQLCaret) {
            $new = $this->select;
            $this->select = new SQLOperator($func, $new, $this);
            return $new;
        }
        throw new Exception('public function append_comma()');
    }
}

class SQLDelete extends SQLStatement
{
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0;
        }
    }
    
    public function append_from()
    {
        if (!$this->from)
            $this->from = new SQLCaret($this);
        
        if ($this->from instanceof SQLCaret)
            return $this->from;

        throw new Exception('public function append_from()');
    }
    
    public function append_where()
    {
        if (!$this->where) {
            $this->where = new SQLCaret($this);
            return $this->where;
        }
        
        throw new Exception('public function append_where()');
    }
    
    public function append_group()
    {
        if (!$this->group) {
            $this->group = new SQLCaret($this);
            return $this->group;
        }
        
        throw new Exception('public function append_group()');
    }
    
    public function append_having()
    {
        if (!$this->having) {
            $this->having = new SQLCaret($this);
            return $this->having;
        }
        
        throw new Exception('public function append_having()');
    }
    
    public function append_order()
    {
        if (!$this->order) {
            $this->order = new SQLCaret($this);
            return $this->order;
        }
        
        throw new Exception('public function append_order()');
    }
    
    public function append_limit()
    {
        if (!$this->limit) {
            $this->limit = new SQLCaret($this);
            return $this->limit;
        }
        
        throw new Exception('public function append_limit()');
    }
    
    public function append_offset()
    {
        if (!$this->offset) {
            $this->offset = new SQLCaret($this);
            return $this->offset;
        }
        
        throw new Exception('public function append_offset()');
    }
    
    public function __toString()
    {
        $sql = "delete from $this->from";
        $where = $this->where;
        if ($where) {
            $sql .= " where $where";
        }
        
        $group = $this->group;
        if ($group) {
            $sql .= " group by $group";
            $having = $this->having;
            if ($having) {
                $sql .= " having $having";
            }
        }
        
        $order = $this->order;
        if ($order) {
            $sql .= " order by $order";
        }
        
        $limit = $this->limit;
        if ($limit) {
            $sql .= " limit $limit";
            
            $offset = $this->offset;
            if ($offset) {
                $sql .= " offset $offset";
            }
        }
        
        return $sql;
    }
    
    public function jsonSerialize()
    {
        $dict = parent::jsonSerialize();
        $dict['delete'] = true;
        return $dict;
    }
}

class SQLWith extends SQL
{
    public $with;
    public $sql;
    public function __construct($with, $sql, $parent = null)
    {
        parent::__construct($parent);
        $this->with = $with;
        $this->sql = $sql;
        $with->parent = $this;
        $sql->parent = $this;
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case "stack_precedence":
                return 0;
        }
    }
    
    public function __toString()
    {
        $sql = $this->sql;
        $with = $this->with;
        if ($with) {
            $sql = "with $with $sql";
        }
        return $sql;
    }
    
    public function replace($old, $new)
    {
        if ($this->with === $old) {
            $this->with = $new;
        }
        elseif ($this->sql === $old) {
            $this->sql = $new;
        }
        else {
            throw new Exception('public function replace($old, $new)');
        }
        if (!$new->parent)
            $new->parent = $this;
    }
    
    public function jsonSerialize()
    {
        $dict = $this->sql->jsonSerialize();
        $dict['with'] = $this->with->jsonSerialize();
        return $dict;
    }
    
    public function append($type)
    {
        if (is_string($type)) {
            $new = new SQLCaret();
            $this->sql = new $type($new);
            $this->sql->parent = $this;
            return $new;
        }
        
        throw new Exception('public function append($type)');
    }
}


function parseSQL() {
//     $sql = "with _t as (with _t as (select json_remove(json_unquote(concat('[', group_concat(json_quote(pn)), ']')), '$[0]') as pn from corpus.markush group by text having count(*) > 1) select _s.pn from _t cross join json_table(pn, '$[*]' columns(pn varchar(36) path '$')) as _s) select pn, text from corpus.markush where pn in (select pn from _t) limit 1000";
    $sql = "with _t as (with _t as (select json_remove(json_unquote(concat('[', group_concat(json_quote(cast(id as char))), ']')), '$[0]') as ids from axiom.latex_ group by latex having count(*) > 1)select id from _t cross join json_table(ids, '$[*]' columns(id int path '$')) as _s)delete from axiom.latex_ where id in (select id from _t)";
    $expr = SQL::compile($sql);
    $expr->jsonSerialize();
    echo std\encode($expr);
}

//parseSQL();
?>