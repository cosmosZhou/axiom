<?php
// cartesian product
namespace itertools;

function product($arrays, $index = 0, $current = [])
{
    // Base case: if index equals the number of arrays, yield the combination
    if ($index === count($arrays)) {
        yield $current;
    } else {
        // Recursive case: iterate through the current array and recurse
        foreach ($arrays[$index] as $value) {
            // Append the current value to the combination
            $current[] = $value;
            // Recurse with the next index
            yield from product($arrays, $index + 1, $current);
            // Backtrack: remove the last element for the next iteration
            array_pop($current);
        }
    }
}
