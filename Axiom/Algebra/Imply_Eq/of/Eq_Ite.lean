import Axiom.Basic
open Algebra


@[main]
private lemma main
  [Decidable p]
  {x a b: α}
-- given
  (h : x = if p then a else b) :
-- imply
  p → x = a := by
-- proof
  intro hp
  simp [h, hp]


-- created on 2025-01-12
