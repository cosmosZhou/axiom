import Lemma.Algebra.Gt.of.Gt.Ge
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α}
  {n : ℕ}
-- given
  (h : x > y + n) :
-- imply
  x > y := by
-- proof
  have : y + n ≥ y := by
    simp
  apply Gt.of.Gt.Ge h this


-- created on 2025-04-27
