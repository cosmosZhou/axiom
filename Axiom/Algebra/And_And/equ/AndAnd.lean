import Axiom.Algebra.AndAnd.equ.And_And
open Algebra


@[main]
private lemma main :
-- imply
  p ∧ q ∧ r ↔ (p ∧ q) ∧ r :=
-- proof
  AndAnd.equ.And_And.symm


-- created on 2024-07-01
