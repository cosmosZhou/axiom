import sympy.concrete.expr_with_limits.lamda
import Lemma.Algebra.PushCons.eq.Cons_Push
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∀ (f : ℕ → α), [i < n + 1] f i = ([i < n] f i).push (f n) := by
-- proof
  induction n with
  | zero =>
    intro f
    simp [Lamda, List.Vector.push]
  | succ n ih =>
    intro f
    calc
      [i < n + 1 + 1] f i = [i < n + 2] f i := rfl
      _ = f 0 ::ᵥ [i < n + 1] f (i + 1) := by rw [Lamda]
      _ = f 0 ::ᵥ ([i < n] f (i + 1)).push (f (n + 1)) := by
        rw [ih (λ i => f (i + 1))]
      _ = (f 0 ::ᵥ [i < n] f (i + 1)).push (f (n + 1)) := by
        rw [PushCons.eq.Cons_Push]
      _ = ([i < n + 1] f i).push (f (n + 1)) := by rw [Lamda]


-- created on 2024-12-22
