<?php
function test() {
    $old = "(if|when)(?![{}]+(un)?[a-z]+(sent|ed|ary))......*(}......*\S+......*)+";
    $new = "(if|when)(?![{}]+(un)?[a-z]+(sent|ed|ary))......*{{{{{{(}......*\S+......*)+}}}}}}";
    [$old, $new] = transform_infix($old, $new);
//     [$old, $new] = transform_infix($old, $new, true, true);
    echo("\$old = ".$old);
    echo("\$new = ".$new);    
}

function test_ufn() {
    $old = "\d+}[—–-][{}]+{\d+.....*}";
    $old = SyntaxMatcher::transform($old);
    echo("\$old = ".$old);
}

require '../std.php';
require './compile.php';
require './balancedMatch.php';
require './Lexeme.php';
require './SyntaxMatcher.php';

test();
// Regex::test();
?>