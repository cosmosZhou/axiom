import Axiom.Basic


@[main]
private lemma main
  {x a b : α}
  (h : x = a ∧ p ∨ x = b ∧ ¬p) :
-- imply
  p ∨ x = b := by
-- proof
  cases h with
  | inl h =>
    exact Or.inl h.right
  | inr h =>
    exact Or.inr h.left


-- created on 2025-01-12
