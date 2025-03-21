import Axiom.Algebra.GeDivS.of.Ge.Gt_0
import Axiom.Algebra.Div.eq.One.of.Gt_0
import Axiom.Algebra.Gt.of.Ge.Gt
import Axiom.Algebra.LeDivS.of.Le.Gt_0
import Axiom.Algebra.DivDiv.eq.Inv.of.Ne_0
import Axiom.Algebra.Ne.of.Gt
import Axiom.Algebra.Div1.eq.Inv
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a : α}
-- given
  (h₀ : a > 0)
  (h₁ : x ≥ a) :
-- imply
  x⁻¹ ≤ a⁻¹ := by
-- proof
  have := GeDivS.of.Ge.Gt_0 h₁ h₀
  simp [Div.eq.One.of.Gt_0 h₀] at this
  have h_Gt_0 := Gt.of.Ge.Gt h₁ h₀
  have := LeDivS.of.Le.Gt_0 this h_Gt_0
  rw [DivDiv.eq.Inv.of.Ne_0 (Ne.of.Gt h_Gt_0)] at this
  rw [Div1.eq.Inv] at this
  assumption


-- created on 2025-03-03
-- updated on 2025-03-15
