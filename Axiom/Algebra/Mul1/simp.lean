import Axiom.Basic

namespace Algebra.Mul1

@[simp]
theorem simp
  [MulOneClass M]
  {a : M} :
-- imply
  1 * a = a := by
-- proof
  rw [one_mul]


end Algebra.Mul1

-- created on 2024-07-01
