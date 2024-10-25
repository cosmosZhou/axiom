import Mathlib.Tactic
import Axiom.sympy.core.containers.list
import Axiom.algebra.all.then.all.fn

namespace algebra.is_uniform.then.is_uniform


theorem map
  [DecidableEq α] [DecidableEq β]
  {s : List α}
-- given
  (h: s is uniform)
  (f : α → β) :
-- imply
  s.map f is uniform := by
  induction s with
  | nil =>
    -- Base case: s = []
    simp [List.is_uniform]
  | cons x s _ =>
    -- simp [List.is_uniform] at *
    simp [List.is_uniform]

    exact algebra.all.then.all.fn h

end algebra.is_uniform.then.is_uniform
open algebra.is_uniform.then.is_uniform
