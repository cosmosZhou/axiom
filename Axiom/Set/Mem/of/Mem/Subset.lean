import Axiom.Basic


@[main]
private lemma main
  {x : α}
  {A B : Set α}
-- given
  (h₀ : x ∈ A)
  (h₁ : A ⊆ B) :
-- imply
  x ∈ B :=
-- proof
  h₁ h₀


-- created on 2025-03-02
