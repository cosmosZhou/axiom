import Axiom.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∃ x : α, p x ∨ q x) :
-- imply
  (∃ x : α, p x) ∨ (∃ x : α, q x) := by
-- proof
  let ⟨x, hpq⟩ := h
  cases hpq with
  | inl hp =>
    exact Or.inl ⟨x, hp⟩
  | inr hq =>
    exact Or.inr ⟨x, hq⟩


-- created on 2024-07-01
