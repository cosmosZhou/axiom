import Axiom.Algebra.Any_Not.equ.NotAll
open Algebra


@[simp, main]
private lemma main
  {p : α → Prop} :
-- imply
  (¬∀ x : α, p x) ↔ ∃ x : α, ¬p x :=
-- proof
  Any_Not.equ.NotAll.symm


-- created on 2024-07-01
