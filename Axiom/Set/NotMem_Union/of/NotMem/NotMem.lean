import Axiom.Basic


@[main]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h₀ : e ∉ A)
  (h₁ : e ∉ B) :
-- imply
  e ∉ A ∪ B := by
-- proof
  intro h
  -- By the definition of union, h : e ∈ A ∪ B implies e ∈ A ∨ e ∈ B.
  cases' h with hA hB <;>
    contradiction


-- created on 2025-04-04
