import Axiom.Basic

namespace Algebra.Add

theorem comm
  [AddCommMagma α]
  {a b : α} :
-- imply
  a + b = b + a := by
-- proof
  apply add_comm


end Algebra.Add

-- created on 2024-07-01
