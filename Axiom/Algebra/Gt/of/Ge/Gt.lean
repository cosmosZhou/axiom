import Axiom.Basic


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : b > c) :
-- imply
  a > c :=
-- proof
  gt_of_ge_of_gt h₀ h₁


-- created on 2025-01-17
