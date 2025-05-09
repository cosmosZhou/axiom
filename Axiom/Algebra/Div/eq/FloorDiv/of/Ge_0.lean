import Axiom.Algebra.Div.eq.FloorDiv.of.Gt_0
import Axiom.Algebra.Gt.of.Ge.Ne
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
  have := Gt.of.Ge.Ne h h_Eq_0
  apply Div.eq.FloorDiv.of.Gt_0 this


-- created on 2025-03-20
-- updated on 2025-03-30
