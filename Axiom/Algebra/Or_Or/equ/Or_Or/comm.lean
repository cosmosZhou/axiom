import Axiom.Algebra.Or_Or.equ.OrOr
open Algebra


@[main]
private lemma main :
-- imply
  a ∨ b ∨ c ↔ b ∨ a ∨ c := by
-- proof
  rw [Or_Or.equ.OrOr]
  rw [Or.comm (b := b)]
  rw [OrOr.equ.Or_Or]


-- created on 2024-07-01
