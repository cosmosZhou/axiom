import Axiom.Basic

namespace Algebra.MulAdd.eq

theorem AddMulS
  [Mul α] [Add α] [RightDistribClass α]
  {a b c : α} :
-- imply
  (a + b) * c = a * c + b * c := by
-- proof
  rw [right_distrib]



end Algebra.MulAdd.eq

-- created on 2024-07-01
