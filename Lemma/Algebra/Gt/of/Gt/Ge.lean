import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b ≥ c) :
-- imply
  a > c :=
-- proof
  gt_of_gt_of_ge h₀ h₁


-- created on 2024-11-29
