import sympy.tensor.tensor
import Lemma.Basic


@[main]
private lemma main
  [NonUnitalSemiring α]
  {L : Tensor α [l, m]}
  {M : Tensor α [m, n]}
  {N : Tensor α [n, o]} :
-- imply
  L @ M @ N = L @ (M @ N) := by
-- proof
  -- apply Matrix.mul_assoc
  sorry


-- created on 2025-05-03
