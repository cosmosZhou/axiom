import Axiom.Algebra.AndImplyS_Eq.of.Eq_Ite
import Axiom.Algebra.Eq_Ite.of.AndImplyS_Eq
open Algebra


@[main]
private lemma main
  [Decidable p]
  {x a b: α} :
-- imply
  (x = if p then a else b) ↔ (p → x = a) ∧ (¬p → x = b) :=
-- proof
  ⟨AndImplyS_Eq.of.Eq_Ite, Eq_Ite.of.AndImplyS_Eq⟩


-- created on 2025-01-12
