import Axiom.Algebra.Any.equ.NotAll_Not
open Algebra


@[simp, main]
private lemma main
  {p : α → Prop} :
-- imply
  (¬∀ x : α, ¬p x) ↔ ∃ x : α, p x :=
-- proof
  Any.equ.NotAll_Not.symm


-- created on 2024-07-01
