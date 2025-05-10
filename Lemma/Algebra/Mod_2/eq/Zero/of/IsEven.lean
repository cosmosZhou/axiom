import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n is even) :
-- imply
  n % 2 = 0 :=
-- proof
  Int.even_iff.mp h


-- created on 2025-03-05
