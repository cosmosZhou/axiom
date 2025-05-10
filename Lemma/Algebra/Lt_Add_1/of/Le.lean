import sympy.polys.domains
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x ≤ y) :
-- imply
  x < y + 1 :=
-- proof
  IntegerRing.lt_succ_of_le h


-- created on 2025-03-28
