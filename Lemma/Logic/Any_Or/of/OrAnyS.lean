import Lemma.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : (∃ x : α, p x) ∨ (∃ x : α, q x)) :
-- imply
  ∃ x : α, p x ∨ q x := by
-- proof
  cases h with
  | inl h_p =>
    let ⟨x, hp⟩ := h_p
    exact ⟨x, Or.inl hp⟩
  | inr h_q =>
    let ⟨x, hq⟩ := h_q
    exact ⟨x, Or.inr hq⟩


-- created on 2024-07-01
