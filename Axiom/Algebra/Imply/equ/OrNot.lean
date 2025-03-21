import Axiom.Algebra.OrNot.of.Imply
import Axiom.Algebra.Imply.of.OrNot
open Algebra


@[main]
private lemma main :
-- imply
  (p → q ↔ ¬p ∨ q)  :=
-- proof
  ⟨OrNot.of.Imply, Imply.of.OrNot⟩


-- created on 2024-07-01
