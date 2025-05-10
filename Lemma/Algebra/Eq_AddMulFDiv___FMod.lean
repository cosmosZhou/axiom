import sympy.functions.elementary.integers
import Lemma.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n = n // d * d + n.fmod d := by
-- proof
  apply Eq.symm
  rw [Mul.comm]
  apply Int.fdiv_add_fmod n d


-- created on 2025-03-21
