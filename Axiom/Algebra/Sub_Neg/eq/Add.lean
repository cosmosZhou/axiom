import Axiom.Algebra.Add.eq.Sub_Neg
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  a - -b = a + b := by
-- proof
  rw [Add.eq.Sub_Neg]


-- created on 2025-03-16
