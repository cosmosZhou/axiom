import Axiom.Basic


@[main]
private lemma main
  {x a b : α}
  (h : x = a ∧ p ∨ x = b ∧ ¬p) :
-- imply
  ¬p ∨ x = a := by
-- proof
  cases h with
  | inl h =>
    exact Or.inr h.left
  | inr h =>
    exact Or.inl h.right


-- created on 2025-01-12
