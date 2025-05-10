import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  {x : ℤ}
-- given
  (h : x > 0) :
-- imply
  sign x = 1 := by
-- proof
  apply Int.sign_eq_one_of_pos h


-- created on 2025-03-30
