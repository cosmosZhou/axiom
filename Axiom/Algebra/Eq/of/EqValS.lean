import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
  {a b: List.Vector α n}
-- given
  (h : a.val = b.val) :
-- imply
  a = b := by
-- proof
  apply List.Vector.eq a b h


-- created on 2024-07-01
-- updated on 2025-05-08
