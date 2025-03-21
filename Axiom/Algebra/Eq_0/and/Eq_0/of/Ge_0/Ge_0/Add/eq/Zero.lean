import Axiom.Algebra.NotAnd.equ.OrNotS
import Axiom.Algebra.NotEq.equ.Ne
import Axiom.Algebra.Gt.of.Ne.Ge
import Axiom.Algebra.Add.gt.Zero.of.Gt_0.Ge_0
import Axiom.Algebra.Add.gt.Zero.of.Ge_0.Gt_0
import Axiom.Algebra.Ne.of.Gt
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x y : α}
-- given
  (h_x : x ≥ 0)
  (h_y : y ≥ 0)
  (h_Add : x + y = 0) :
-- imply
  x = 0 ∧ y = 0 := by
-- proof
  by_contra h
  rw [NotAnd.equ.OrNotS] at h
  rw [NotEq.equ.Ne, NotEq.equ.Ne] at h
  cases h with
  | inl h => 
    have := Gt.of.Ne.Ge h h_x
    have := Add.gt.Zero.of.Gt_0.Ge_0 this h_y
    have := Ne.of.Gt this
    contradiction
  | inr h => 
    have := Gt.of.Ne.Ge h h_y
    have := Add.gt.Zero.of.Ge_0.Gt_0 h_x this
  
    have := Ne.of.Gt this
    contradiction


-- created on 2025-01-17
