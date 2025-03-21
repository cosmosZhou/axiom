import Axiom.Algebra.Le.of.Lt.relax
open Algebra


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≥ y := by
-- proof
  exact Le.of.Lt.relax h


-- created on 2024-07-01
