import Axiom.sympy.core.containers.vector
open Mathlib
namespace Algebra.Eq_.Dot


@[simp]
theorem Zero
  [Add α] [Zero α] [Mul α]
  {x y : Vector α 0} :
-- imply
  x ⬝ y = 0 := by
-- proof
  match x, y with
  | ⟨x, xProperty⟩, ⟨y, yProperty⟩ =>
    simp [Vector.dot] at xProperty yProperty
    simp [Vector.dot, xProperty, yProperty]


end Algebra.Eq_.Dot

-- created on 2024-07-01
