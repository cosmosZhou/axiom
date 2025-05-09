import Axiom.Algebra.Le.of.Lt
import Axiom.Algebra.Div.ge.Zero.of.Le_0.Le_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b : α}
-- given
  (h₀ : a ≤ 0)
  (h₁ : b < 0) :
-- imply
  a / b ≥ 0 := by
-- proof
  have := Le.of.Lt h₁
  apply Div.ge.Zero.of.Le_0.Le_0 h₀ this


-- created on 2025-03-30
