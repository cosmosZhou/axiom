import Lemma.Algebra.EqDivS.of.Eq
import Lemma.Algebra.Or_Eq_NegSqrt.of.EqSquare
import Lemma.Algebra.NegDiv.eq.DivNeg
open Algebra


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : a * x² = c) :
-- imply
  x = √(a * c) / a ∨
    x = -√(a * c) / a := by
-- proof
  have h₁ := EqDivS.of.Eq h₁ a
  simp [h₀] at h₁
  have h := Or_Eq_NegSqrt.of.EqSquare h₁
  have h_EqSqrt : √(c / a) = √c / √a := by
    simp [Root.sqrt]
    sorry
  have h_Eq : √(a * c) / a = √(c / a) := by
    sorry
  sorry


-- created on 2024-07-01
