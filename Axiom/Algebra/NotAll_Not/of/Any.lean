import Axiom.Basic


@[main]
private lemma main
  {p : α → Prop}
-- given
  (h : ∃ x : α, p x) :
-- imply
  ¬∀ x : α, ¬p x := by
-- proof
  intro h_All
  let ⟨x, h⟩ := h
  have h := h_All x
  contradiction


-- created on 2024-07-01
