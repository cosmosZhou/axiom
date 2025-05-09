import Axiom.Algebra.Inv.gt.Zero.of.Gt_0
import Axiom.Algebra.Mul.lt.Zero.of.Lt_0.Gt_0
import Axiom.Algebra.Mul_Inv.eq.Div
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x y : α}
-- given
  (h₀ : x < 0)
  (h₁ : y > 0) :
-- imply
  x / y < 0 := by
-- proof
  have h₁ := Inv.gt.Zero.of.Gt_0 h₁
  have := Mul.lt.Zero.of.Lt_0.Gt_0 h₀ h₁
  rw [Mul_Inv.eq.Div] at this
  assumption


-- created on 2025-03-30
