import Axiom.Algebra.LtMod.of.Gt_0
import Axiom.Algebra.LtDivS.of.Lt.Gt_0
import Axiom.Algebra.Div.eq.One.of.Gt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  (n % d : ℤ) / (d : ℚ) < 1 := by
-- proof
  have := LtMod.of.Gt_0 (n := n) h
  have : ((n % d) : ℤ) < (d : ℚ) := by
    simp [this]
  have h : (d : ℚ) > 0 := by simp [h]
  have := LtDivS.of.Lt.Gt_0 this h
  rw [Div.eq.One.of.Gt_0 h] at this
  assumption


-- created on 2025-03-20
