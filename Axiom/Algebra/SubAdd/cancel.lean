import Axiom.Basic

namespace Algebra.SubAdd

theorem cancel
  [AddGroup α]
  {a b : α} :
-- imply
  a + b - b = a := by
-- proof
  apply add_sub_cancel_right


end Algebra.SubAdd

-- created on 2024-11-27
