import Axiom.Algebra.Abs.eq.SqrtAddSqaureS
import Axiom.Algebra.Le_0.of.EqSqrt_0
import Axiom.Algebra.AddSquareS.ge.Zero
import Axiom.Algebra.Eq.of.Ge.Le
import Axiom.Algebra.Eq.of.EqReS.EqImS
import Axiom.Algebra.Eq_0.and.Eq_0.of.AddSquareS.eq.Zero
open Algebra


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : abs z = 0) :
-- imply
  z = 0 := by
-- proof
  have := Abs.eq.SqrtAddSqaureS (z := z)
  rw [h] at this
  have h_Le_0 := Le_0.of.EqSqrt_0 this.symm
  have h_Ge_0 := AddSquareS.ge.Zero (a := re z) (b := im z)
  have := Eq.of.Ge.Le h_Ge_0 h_Le_0
  have ⟨left, right⟩ := Eq_0.and.Eq_0.of.AddSquareS.eq.Zero this
  apply Eq.of.EqReS.EqImS <;>
  ·
    simp
    assumption


-- created on 2025-01-16
-- updated on 2025-01-26
