import Axiom.Algebra.False.of.AndNot
open Algebra


@[main]
private lemma main
-- given
  (h : p ∧ ¬p) :
-- imply
  False := by
-- proof
  rw [And.comm] at h
  apply False.of.AndNot h


-- created on 2024-07-01
