import Axiom.Basic
open Algebra


@[main]
private lemma main
  [Neg α]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  -x = -y := by
-- proof
  rw [h]


-- created on 2025-03-16
