import Axiom.Algebra.Le.of.NotGt
import Axiom.Algebra.NotGt.of.Le
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  ¬a > b ↔ a ≤ b := 
-- proof
  ⟨Le.of.NotGt, NotGt.of.Le⟩


-- created on 2025-04-18
