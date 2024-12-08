import Axiom.Algebra.MulAdd.eq.AddMulS

namespace Algebra.AddMulS.eq

theorem MulAdd
  [Mul α] [Add α] [RightDistribClass α]
  {a b c : α} :
-- imply
  a * c + b * c = (a + b) * c := by
-- proof
  rw [MulAdd.eq.AddMulS]



end Algebra.AddMulS.eq

-- created on 2024-07-01
