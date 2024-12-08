import Axiom.Basic

namespace Algebra.Mul

theorem comm
  [CommMagma α]
  {a b : α} :
-- imply
  a * b = b * a := by
-- proof
  apply mul_comm


end Algebra.Mul

-- created on 2024-07-01
