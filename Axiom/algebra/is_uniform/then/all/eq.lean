import Mathlib.Tactic
import Axiom.sympy.core.containers.list

namespace algebra.is_uniform.then.all

theorem eq
  [DecidableEq α]
  {s : List α}
-- given
  (h: s is uniform)
  (default: α):
-- imply
  ∀ x ∈ s, x = s.headD default := by
  match s with
  | List.nil => simp [List.is_uniform] at *
  | List.cons x xs =>
    simp [List.is_uniform] at *
    intro x x_in_s
    exact h x x_in_s


end algebra.is_uniform.then.all
open algebra.is_uniform.then.all
