import Axiom.Basic

namespace Algebra.Sub.eq

@[simp]
theorem Zero
  [AddGroup α]
  {a : α} :
-- imply
  a - a = 0 := by
-- proof
  rw [sub_self]

end Algebra.Sub.eq

-- created on 2024-07-01
