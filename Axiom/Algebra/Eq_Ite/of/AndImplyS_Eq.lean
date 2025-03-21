import Axiom.Basic
open Algebra


@[main]
private lemma main
  [Decidable p]
  {x a b: α}
-- given
  (h : (p → x = a) ∧ (¬p → x = b)) :
-- imply
  x = if p then a else b := by
-- proof
  by_cases hp: p <;>
  ·
    simp [hp] at *
    exact h


-- created on 2025-01-12
