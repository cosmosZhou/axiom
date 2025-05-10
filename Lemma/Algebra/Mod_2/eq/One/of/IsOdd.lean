import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n is odd) :
-- imply
  n % 2 = 1 :=
-- proof
  Int.not_even_iff.mp h


-- created on 2025-03-05
