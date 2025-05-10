import Lemma.Algebra.LeInvS.of.Gt_0.Ge
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a : α}
-- given
  (h₀ : a > 0)
  (h₁ : x ≥ a) :
-- imply
  a⁻¹ ≥ x⁻¹ :=
-- proof
  LeInvS.of.Gt_0.Ge h₀ h₁


-- created on 2025-03-15
