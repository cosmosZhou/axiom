import Axiom.Algebra.Div.eq.One.of.Gt_0
import Axiom.Algebra.DivDiv.eq.Inv.of.Ne_0
import Axiom.Algebra.Ne.of.Gt
import Axiom.Algebra.Div1.eq.Inv
import Axiom.Algebra.GtDivS.of.Gt.Gt_0
import Axiom.Algebra.Gt.of.Gt.Gt
import Axiom.Algebra.LtDivS.of.Lt.Gt_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a : α}
-- given
  (h₀ : a > 0)
  (h₁ : x > a) :
-- imply
  x⁻¹ < a⁻¹ := by
-- proof
  have := GtDivS.of.Gt.Gt_0 h₁ h₀
  simp [Div.eq.One.of.Gt_0 h₀] at this
  have h_Gt_0 := Gt.of.Gt.Gt h₁ h₀
  have := LtDivS.of.Lt.Gt_0 this h_Gt_0
  rw [DivDiv.eq.Inv.of.Ne_0 (Ne.of.Gt h_Gt_0)] at this
  rw [Div1.eq.Inv] at this
  assumption


-- created on 2025-03-15
