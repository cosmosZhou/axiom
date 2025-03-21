import Axiom.Algebra.Mod.ge.Zero.of.Gt_0
import Axiom.Algebra.Div.eq.AddDiv___Mod
import Axiom.Algebra.GeDivS.of.Ge.Gt_0
import Axiom.Algebra.Ge.of.Eq_Add.Ge_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n / (d : ℚ) ≥ (n / d : ℤ) := by
-- proof
  have h_Ge_0 := Mod.ge.Zero.of.Gt_0 (n := n) h
  have h_Ge_0 : (n % d : ℤ) ≥ (0 : ℚ) := by
    simp [h_Ge_0]
  have h_Eq := Div.eq.AddDiv___Mod (n := n) (d := d)
  have h_GeDivS := GeDivS.of.Ge.Gt_0 h_Ge_0 (by simp [h] : (d : ℚ) > 0)
  norm_num at h_GeDivS
  exact Ge.of.Eq_Add.Ge_0 h_Eq h_GeDivS


-- created on 2025-03-20
