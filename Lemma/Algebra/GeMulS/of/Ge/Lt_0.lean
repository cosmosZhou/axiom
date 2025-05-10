import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.LeMulS.of.Ge.Le_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x < 0) :
-- imply
  a * x ≤ b * x := by
-- proof
  have := Le.of.Lt h₁
  apply LeMulS.of.Ge.Le_0 h₀ this


-- created on 2025-03-23
