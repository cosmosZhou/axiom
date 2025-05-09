import sympy.polys.domains
import Axiom.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≥ y) :
-- imply
  x > y - 1 := by
-- proof
  -- Use the `linarith` tactic to solve the inequality involving integers.
  linarith


-- created on 2025-03-28
