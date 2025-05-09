import Axiom.Algebra.NotGe.of.Lt
open Algebra


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  ¬a ≤ b := by
-- proof
  apply NotGe.of.Lt h


-- created on 2025-03-29
