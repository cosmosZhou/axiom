import Lemma.Logic.NotAnd.is.OrNotS
import Lemma.Logic.NotEq.is.Ne
import Lemma.Algebra.Gt.of.Ge.Ne
import Lemma.Algebra.Add.gt.Zero.of.Gt_0.Ge_0
import Lemma.Algebra.Add.gt.Zero.of.Ge_0.Gt_0
import Lemma.Algebra.Ne.of.Gt
open Algebra Logic


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α}
-- given
  (h_x : x ≥ 0)
  (h_y : y ≥ 0)
  (h_Add : x + y = 0) :
-- imply
  x = 0 ∧ y = 0 := by
-- proof
  by_contra h
  rw [NotAnd.is.OrNotS] at h
  rw [NotEq.is.Ne, NotEq.is.Ne] at h
  cases h with
  | inl h =>
    have := Gt.of.Ge.Ne h_x h
    have := Add.gt.Zero.of.Gt_0.Ge_0 this h_y
    have := Ne.of.Gt this
    contradiction
  | inr h =>
    have := Gt.of.Ge.Ne h_y h
    have := Add.gt.Zero.of.Ge_0.Gt_0 h_x this
    have := Ne.of.Gt this
    contradiction


-- created on 2025-01-17
-- updated on 2025-03-30
