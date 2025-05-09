import Axiom.Algebra.SubNeg.eq.NegAdd
open Algebra


@[main]
private lemma main
  [SubtractionCommMonoid α]
  {a b : α} :
-- imply
  -(a + b) = -a - b := by
-- proof
  rw [SubNeg.eq.NegAdd]


-- created on 2025-03-30
