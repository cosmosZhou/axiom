import Axiom.Basic


/--
This lemma demonstrates the associativity of addition in an additive semigroup, showing that the expression `a + b + c` is equal to `a + (b + c)`. 
The proof utilizes the `add_assoc` axiom inherent to the structure of an additive semigroup to rearrange the parentheses, thereby establishing the equality.
-/
@[main]
private lemma main
  [AddSemigroup α]
  {a b : α} :
-- imply
  a + b + c = a + (b + c) := by
-- proof
  rw [add_assoc]


-- created on 2024-07-01
-- updated on 2025-04-04
