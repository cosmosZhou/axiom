import Axiom.Algebra.MulMul.eq.Mul_Mul
open Algebra


/--
This lemma confirms the associativity of multiplication in a semigroup by showing that `a * (b * c)` equals `a * b * c`. 
It provides the reverse direction of the associativity axiom, enabling flexible rearrangement of multiplicative expressions.
-/
@[main]
private lemma main
  [Semigroup α]
  {a b : α} :
-- imply
  a * (b * c) = a * b * c := by
-- proof
  rw [MulMul.eq.Mul_Mul]


-- created on 2024-07-01
-- updated on 2025-04-04
