import Axiom.sympy.core.containers.list

namespace Mathlib.Vector

-- Implement the instance for Vector
instance : IsConstant (Vector α n) where
  is_constant v := v.val is constant


def dot [Add α] [Zero α] [Mul α] (v1 v2 : Vector α n) : α :=
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

/--
def sum [Add α] [Zero α] (v : Vector α n) : α :=
  v.val.sum
-/

def sum [Add α] [Zero α] : Vector α n → α
  | ⟨v, _⟩ => v.sum

def headD : Vector α n → α → α
  | ⟨v, _⟩, d => v.headD d

end Mathlib.Vector
