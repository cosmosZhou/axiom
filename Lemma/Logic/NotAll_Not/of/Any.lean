import Lemma.Basic


@[main]
private lemma finset
  {p : ι → Prop}
  {s : Finset ι}
-- given
  (h : ∃ x : s, p x) :
-- imply
  ¬∀ x : s, ¬p x := by
-- proof
  intro h_All
  let ⟨x, h⟩ := h
  have h := h_All x
  contradiction


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
