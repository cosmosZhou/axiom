import Axiom.Algebra.And_Imply_Eq_DivNeg.of.EqAddMul___0.simple
import Axiom.Algebra.Or_Eq_Div_Mul2_Sub_Sqrt.of.Ne_0.EqAddMul_Square_Mul__0
open Algebra


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h : a * x² + b * x + c = 0) :
-- imply
  (a = 0 ∧ b = 0 → c = 0) ∧
  (a = 0 ∧ b ≠ 0 → x = -c / b) ∧
  (a ≠ 0 →
    let Δ : ℂ := b² - 4 * a * c
    (x = (-b + √Δ) / (2 * a) ∨
      x = (-b - √Δ) / (2 * a))
    ) := by
-- proof
  constructor
  -- case left
  intro ha
  rw [ha.left] at h
  rw [ha.right] at h
  simp at h
  exact h
  -- case right
  constructor
  -- case right.left
  intro ha
  rw [ha.left] at h
  simp at h
  exact (And_Imply_Eq_DivNeg.of.EqAddMul___0.simple h).right ha.right
  -- case right.right
  intro ha
  apply Or_Eq_Div_Mul2_Sub_Sqrt.of.Ne_0.EqAddMul_Square_Mul__0 ha h


-- created on 2024-07-01
-- updated on 2025-03-16
