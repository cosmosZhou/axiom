import Lemma.Algebra.Sign.eq.One.of.Gt_0
import Lemma.Algebra.Ge_Add_1.of.Gt
open Algebra


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d > 0) :
-- imply
  sign d ≤ d := by
-- proof
  have := Sign.eq.One.of.Gt_0 h
  rw [this]
  have := Ge_Add_1.of.Gt h
  simp_all


-- created on 2025-03-30
