import Axiom.Algebra.Add_Neg.eq.Sub
open Algebra


@[main]
private lemma main
  [SubtractionCommMonoid α]
  {a b : α} :
-- imply
  -a - b = -(a + b) := by
-- proof
  -- Use the neg_add lemma which states -(a + b) = -a + -b
  rw [neg_add]
  rw [Add_Neg.eq.Sub]


-- created on 2025-03-27
