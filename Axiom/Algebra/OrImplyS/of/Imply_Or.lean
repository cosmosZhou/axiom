import Axiom.Algebra.Imply.equ.OrNot
import Axiom.Algebra.Or_Or.equ.OrOr
import Axiom.Algebra.Or_Or.equ.Or_Or.comm
open Algebra


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → (q ∨ r)) :
-- imply
  (p → q) ∨ (p → r) := by
-- proof
  rw [Imply.equ.OrNot] at h
  rw [Imply.equ.OrNot]
  rw [Imply.equ.OrNot]
  rw [OrOr.equ.Or_Or]
  rw [Or_Or.equ.Or_Or.comm] at h
  apply Or.inr h


-- created on 2024-07-01
