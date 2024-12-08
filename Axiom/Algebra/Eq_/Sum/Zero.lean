import Axiom.sympy.core.containers.vector

open Mathlib

namespace Algebra.Eq_.Sum

@[simp]
theorem Zero
  [Add α] [Zero α]
  {s : Vector α 0} :
-- imply
  s.sum = 0 := by
-- proof
  match s with
  | ⟨v, property⟩ =>
    simp [Vector.sum] at property
    simp [Vector.sum, property]


end Algebra.Eq_.Sum

-- created on 2024-07-01
