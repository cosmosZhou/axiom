import Axiom.Basic


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b > c) :
-- imply
  a > c :=
-- proof
  gt_trans h₀ h₁


-- created on 2024-11-25
