import Axiom.Algebra.Sub.eq.Add_Neg
open Algebra


@[main]
private lemma main
  [SubNegMonoid α]
  {a b : α} :
-- imply
  a + -b = a - b := by
-- proof
  rw [Sub.eq.Add_Neg]


-- created on 2024-07-01
