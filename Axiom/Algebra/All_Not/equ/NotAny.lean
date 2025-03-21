import Axiom.Algebra.All.equ.NotAny_Not
open Algebra


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (∀ x : α, ¬p x) ↔ ¬∃ x : α, p x := by
-- proof
  rw [All.equ.NotAny_Not]
  simp


-- created on 2024-07-01
