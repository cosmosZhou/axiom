import Lemma.Basic


@[main]
private lemma main
  {r :Prop}
  {p : α → Prop}
-- given
  (h : (∃ x : α, p x) ∧ r) :
-- imply
  ∃ x : α, p x ∧ r := by
-- proof
  let ⟨⟨x, hLeft⟩, hRight⟩ := h
  exact ⟨x, hLeft, hRight⟩


-- created on 2024-07-01
