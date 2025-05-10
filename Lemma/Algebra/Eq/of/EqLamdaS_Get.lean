import sympy.tensor.tensor
import sympy.concrete.expr_with_limits.lamda
import Lemma.Basic


@[main]
private lemma main
  [Inhabited α]
  {x y : Tensor ℕ [n]}
  {a : Tensor α [n]}
-- given
  (h : x = y) :
-- imply
  [i < n] a[x[i]] = [i < n] a[y[i]] := by
-- proof
  simp [h]


-- created on 2025-05-01
