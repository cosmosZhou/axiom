import Axiom.Algebra.Div0.eq.Zero
import Axiom.Algebra.GeDivS.of.Le.Le_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]

  {a b : α}
-- given
  (h₀ : a ≤ 0)
  (h₁ : b ≤ 0) :
-- imply
  a / b ≥ 0 := by
-- proof
  have h := GeDivS.of.Le.Le_0 h₀ h₁
  simp only [Div0.eq.Zero] at h
  exact h


-- created on 2025-03-30
