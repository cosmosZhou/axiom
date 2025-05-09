import Axiom.Algebra.Eq.ou.Lt.of.Le
open Algebra


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  a < b∨ a = b  := by
-- proof
  rw [Or.comm]
  apply Eq.ou.Lt.of.Le h


-- created on 2025-04-26
