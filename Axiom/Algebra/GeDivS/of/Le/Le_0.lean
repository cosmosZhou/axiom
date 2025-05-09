import Axiom.Algebra.Mul_Inv.eq.Div
import Axiom.Algebra.Inv.le.Zero.of.Le_0
import Axiom.Algebra.GeMulS.of.Le.Le_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≤ 0) :
-- imply
  a / x ≥ b / x := by
-- proof
  have : x⁻¹ ≤ 0 := Inv.le.Zero.of.Le_0 h₁
  have := GeMulS.of.Le.Le_0 h₀ this
  rw [
    Mul_Inv.eq.Div,
    Mul_Inv.eq.Div
  ] at this
  exact this


-- created on 2025-03-30
