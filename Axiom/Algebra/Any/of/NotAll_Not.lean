import Axiom.Algebra.Any_Not.of.NotAll
open Algebra


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
