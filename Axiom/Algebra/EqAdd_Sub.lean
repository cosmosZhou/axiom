import Axiom.Algebra.Sub.eq.Add_Neg
open Algebra


@[simp, main]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  a + (b - a) = b := by
-- proof
  simp [Sub.eq.Add_Neg]


-- created on 2025-03-20
