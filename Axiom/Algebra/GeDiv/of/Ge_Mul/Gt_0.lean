import Axiom.Algebra.GeMulS.of.Ge.Gt_0
import Axiom.Algebra.Mul_Inv.eq.Div
import Axiom.Algebra.Inv.gt.Zero.of.Gt_0
import Axiom.Algebra.EqDivMul.of.Ne_0
import Axiom.Algebra.Ne.of.Gt
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x y t : α}
-- given
  (h₀ : y ≥ t * x)
  (h₁ : x > 0) :
-- imply
  y / x ≥ t := by
-- proof
  have : x⁻¹ > 0 := Inv.gt.Zero.of.Gt_0 h₁
  have := GeMulS.of.Ge.Gt_0 h₀ this
  rw [
    Mul_Inv.eq.Div,
    Mul_Inv.eq.Div
  ] at this
  have h_Ne := Ne.of.Gt h₁
  rw [EqDivMul.of.Ne_0 h_Ne] at this
  assumption


-- created on 2025-03-30
