import Axiom.Basic


@[main]
private lemma main
  {s : List α}
  {f₁ f₂ : α → β}
  {f₃ : β → γ}
-- given
  (h : ∀ x ∈ s, f₁ x = f₂ x) :
-- imply
  ∀ x ∈ s, f₃ (f₁ x) = f₃ (f₂ x) := by
-- proof
  intro x x_in_s
  rw [h x x_in_s]


-- created on 2024-07-01
