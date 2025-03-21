import Axiom.Algebra.OrOr.equ.Or_Or
open Algebra


@[main]
private lemma main :
-- imply
  p ∨ q ∨ r ↔ (p ∨ q) ∨ r :=
-- proof
  OrOr.equ.Or_Or.symm


-- created on 2024-07-01
