import Axiom.Algebra.OrAnd.equ.AndOrS
open Algebra


@[main]
private lemma main :
-- imply
  (p ∨ r) ∧ (q ∨ r) ↔ p ∧ q ∨ r :=
-- proof
  OrAnd.equ.AndOrS.symm


-- created on 2024-07-01
