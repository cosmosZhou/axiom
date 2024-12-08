import Axiom.Basic

namespace Algebra.Sub_Add

@[simp]
theorem cancel
  [AddCommGroup α]
  {a b : α} :
-- imply
  a + b - a = b := by
-- proof
  rw [add_sub_cancel_left]


end Algebra.Sub_Add


-- created on 2024-07-01
