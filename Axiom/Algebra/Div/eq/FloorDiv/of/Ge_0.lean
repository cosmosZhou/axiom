import Axiom.Algebra.Div.eq.FloorDiv.of.Gt_0
import Axiom.Algebra.Gt.of.Ne.Ge
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d ≥ 0) :
-- imply
  n / d = ⌊n / (d : ℚ)⌋ := by
-- proof
  by_cases h_Eq_0 : d = 0
  rw [h_Eq_0]
  norm_num
  have := Gt.of.Ne.Ge h_Eq_0 h 
  apply Div.eq.FloorDiv.of.Gt_0 this


-- created on 2025-03-20
