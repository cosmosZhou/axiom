import Axiom.Basic

namespace Algebra.Add_0

@[simp]
theorem simp
  [AddZeroClass α]
  {a : α} :
-- imply
  a + 0 = a := by
-- proof
  rw [add_zero]


end Algebra.Add_0

-- created on 2024-07-01
