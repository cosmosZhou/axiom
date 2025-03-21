import Axiom.Algebra.Any.equ.NotAll_Not
open Algebra


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (∃ x : α, ¬p x) ↔ ¬∀ x : α, p x := by
-- proof
  rw [Any.equ.NotAll_Not]
  simp


-- created on 2024-07-01
