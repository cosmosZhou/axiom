import sympy.concrete.expr_with_limits.lamda
import Lemma.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  ([i < n + 1] f i).tail = [i < n] f (i + 1) := by
-- proof
  rw [Lamda]
  rfl


-- created on 2024-12-22
