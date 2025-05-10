import Lemma.Algebra.Eq_0.of.Norm.eq.Zero
open Algebra


@[main]
private lemma main
  {a : ℂ}
-- given
  (h : a ≠ 0) :
-- imply
  ‖a‖ ≠ 0 := by
-- proof
  by_contra h_Eq_0
  have := Eq_0.of.Norm.eq.Zero h_Eq_0
  contradiction


-- created on 2025-01-16
-- updated on 2025-01-17
