import Axiom.Algebra.Imply.equ.OrNot
open Algebra


@[main]
private lemma main :
-- imply
  (¬p → q ↔ p ∨ q)  := by
-- proof
  rw [Imply.equ.OrNot]
  simp


-- created on 2025-01-12
