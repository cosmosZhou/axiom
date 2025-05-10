import sympy.polys.domains
import Lemma.Algebra.Gt.of.NotLe
import Lemma.Algebra.GeSub_1.of.Gt
import Lemma.Algebra.Lt.of.Lt.Le
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x - 1 < y) :
-- imply
  x ≤ y := by
-- proof
  by_contra h'
  have := Gt.of.NotLe h'
  have := GeSub_1.of.Gt this
  have := Lt.of.Lt.Le h this
  simp at this


-- created on 2025-05-05
-- updated on 2025-05-06
