import Lemma.Algebra.Sub.eq.Add_Neg
open Algebra


/--
This lemma confirms that in a `SubNegMonoid`, the operation of adding the negation of an element `b` to another element `a` is equivalent to subtracting `b` from `a`.
Specifically, it verifies the algebraic identity `a + (-b) = a - b`, ensuring consistency between additive inverses and subtraction within this algebraic structure.
-/
@[main]
private lemma main
  [SubNegMonoid α]
  {a b : α} :
-- imply
  a + -b = a - b := by
-- proof
  rw [Sub.eq.Add_Neg]


-- created on 2024-07-01
-- updated on 2025-04-04
