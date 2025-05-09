import Axiom.Algebra.Lt.of.Le.Ne
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
  have := Lt.of.Le.Ne h h_Eq_0
  apply Div.eq.CeilDiv.of.Lt_0 this


-- created on 2025-03-20
-- updated on 2025-03-30
