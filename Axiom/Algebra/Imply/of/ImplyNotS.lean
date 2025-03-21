import Axiom.Algebra.ImplyNotS.of.Imply
open Algebra


@[main]
private lemma main
-- given
  (h : ¬p → ¬q) :
-- imply
  q → p := by
-- proof
  have h := ImplyNotS.of.Imply h
  simp at h
  exact h


-- created on 2024-07-01
