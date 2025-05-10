import sympy.concrete.expr_with_limits.lamda
import Lemma.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (h: ∀ f : ℕ → α, [i < n + 1] f i = ([i < n] f i).push (f n)) :
-- imply
  ∀ f : ℕ → α, [i < n + 1] f (i + 1) = ([i < n] f (i + 1)).push (f (n + 1)) := by
-- proof
  intro f
  specialize h (fun i => f (i + 1))
  rw [h]


-- created on 2024-12-22
