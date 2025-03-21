import Axiom.Algebra.All_Not.equ.NotAny
open Algebra


@[simp, main]
private lemma main
  {p : α → Prop} :
-- imply
  (¬∃ x : α, p x) ↔ ∀ x : α, ¬p x :=
-- proof
  All_Not.equ.NotAny.symm


-- created on 2024-07-01
