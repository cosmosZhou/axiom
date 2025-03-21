import Axiom.Algebra.Lt.of.Ne.Le
import Axiom.Algebra.Div.eq.CeilDiv.of.Lt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d ≤ 0) :
-- imply
  n / d = ⌈n / (d : ℚ)⌉ := by
-- proof
  by_cases h_Eq_0 : d = 0
  rw [h_Eq_0]
  norm_num
  have := Lt.of.Ne.Le h_Eq_0 h
  apply Div.eq.CeilDiv.of.Lt_0 this


-- created on 2025-03-20
