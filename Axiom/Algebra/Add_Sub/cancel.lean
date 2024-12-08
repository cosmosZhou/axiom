import Axiom.Basic

namespace Algebra.Add_Sub

@[simp]
theorem cancel
  [AddGroup α]
  {a b : α} :
-- imply
  a - b + b = a := by
-- proof
  rw [sub_add_cancel]


end Algebra.Add_Sub

-- created on 2024-07-01
