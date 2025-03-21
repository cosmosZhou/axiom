import Axiom.Algebra.AddDivS.eq.DivAdd
open Algebra


@[main]
private lemma main
  [Field α]
  {x y a : α} :
-- imply
  (x + y) / a = x / a + y / a := by
-- proof
  rw [← AddDivS.eq.DivAdd]


-- created on 2024-07-01
