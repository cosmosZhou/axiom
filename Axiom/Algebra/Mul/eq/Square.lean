import Axiom.Algebra.Square.eq.Mul
open Algebra


/--
This lemma establishes that the product of an element with itself in a monoid is equal to its square. 
It serves as the converse to the axiom `Square.eq.Mul`, enabling the interchange between multiplicative and squared notations.
-/
@[main]
private lemma main
  [Monoid α]
  {x : α} :
-- imply
  x * x = x² := by
-- proof
  rw [Square.eq.Mul]


-- created on 2024-07-01
-- updated on 2025-04-04
