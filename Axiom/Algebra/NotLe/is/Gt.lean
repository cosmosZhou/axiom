import Axiom.Algebra.Lt.of.NotGe
import Axiom.Algebra.NotGe.of.Lt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  (¬a ≤ b) ↔ (a > b) :=
-- proof
  ⟨Lt.of.NotGe, NotGe.of.Lt⟩


-- created on 2025-03-21
