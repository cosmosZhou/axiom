import Lemma.Algebra.LtInvS.of.Gt_0.Ge
import Lemma.Algebra.Sub.lt.Zero.of.Lt
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x y : α}
-- given
  (h₀ : y > 0)
  (h₁ : x > y) :
-- imply
  x⁻¹ - y⁻¹ < 0 := by
-- proof
  have := LtInvS.of.Gt_0.Ge h₀ h₁
  exact Sub.lt.Zero.of.Lt this


-- created on 2025-03-15
