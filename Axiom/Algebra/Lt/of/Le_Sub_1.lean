import sympy.polys.domains
import Axiom.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≤ y - 1) :
-- imply
  x < y := by
-- proof
  linarith


-- created on 2025-03-30
-- updated on 2025-05-07
