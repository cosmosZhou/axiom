import Axiom.Basic

namespace Algebra.Add0

@[simp]
theorem simp
  [AddZeroClass M]
  {a : M} :
-- imply
  0 + a = a := by
-- proof
  rw [zero_add]

end Algebra.Add0

-- created on 2024-07-01
