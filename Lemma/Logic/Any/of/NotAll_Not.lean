import Lemma.Logic.Any_Not.of.NotAll
open Logic


@[main]
private lemma finset
  {p : ι → Prop}
  {s : Finset ι}
-- given
  (h : ¬∀ x : s, ¬p x) :
-- imply
  ∃ x : s, p x := by
-- proof
  have h := Any_Not.of.NotAll h
  simp at h
  let ⟨a, ha, pa⟩ := h
  use ⟨a, ha⟩


@[main]
private lemma main
  {p : α → Prop}
-- given
  (h : ¬∀ x : α, ¬p x) :
-- imply
  ∃ x : α, p x := by
-- proof
  have h := Any_Not.of.NotAll h
  simp at h
  exact h


-- created on 2024-07-01
-- updated on 2025-04-06
