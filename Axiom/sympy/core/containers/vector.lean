import Mathlib.Tactic
import Axiom.sympy.core.containers.list
-- import Axiom.sympy.core.containers.list

namespace Vector

-- Implement the instance for Vector
instance [DecidableEq α] {n : Nat} : IsUniform α (Vector α n) where
  is_uniform := fun v => v.val is uniform


def dot [Add α] [Mul α] [Zero α] {n : ℕ} (v1 v2 : Vector α n) : α :=
  match n, v1, v2 with
  | 0, ⟨[], _⟩, ⟨[], _⟩ => 0
  | n + 1, ⟨x :: xs, h1⟩, ⟨y :: ys, h2⟩ =>
    have h1 : xs.length = n := by
      simp [List.length, h1] at h1
      assumption
    have h2 : ys.length = n := by
      simp [List.length, h2] at h2
      assumption
    x * y + dot ⟨xs, h1⟩ ⟨ys, h2⟩

infix:70 "⬝" => dot

end Vector
