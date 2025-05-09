import Axiom.Algebra.Ge.Ne.is.Gt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  a > b ↔ a ≥ b ∧ a ≠ b :=
-- proof
  Ge.Ne.is.Gt.symm


-- created on 2025-04-18
