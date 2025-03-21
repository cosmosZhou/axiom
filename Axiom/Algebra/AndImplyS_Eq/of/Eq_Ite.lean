import Axiom.Algebra.Imply_Eq.of.Eq_Ite
import Axiom.Algebra.ImplyNot_Eq.of.Eq_Ite
open Algebra


@[main]
private lemma main
  [Decidable p]
  {x a b: α}
-- given
  (h : x = if p then a else b) :
-- imply
  (p → x = a) ∧ (¬p → x = b) := by
-- proof
  constructor
  apply Imply_Eq.of.Eq_Ite h
  apply ImplyNot_Eq.of.Eq_Ite h


-- created on 2025-01-12
