import Axiom.Algebra.AndAndNot.equ.False
open Algebra


@[simp, main]
private lemma main :
-- imply
  (q ∧ ¬p) ∧ p ↔ False := by
-- proof
  rw [And.comm (a := q)]
  apply AndAndNot.equ.False


-- created on 2024-07-01
