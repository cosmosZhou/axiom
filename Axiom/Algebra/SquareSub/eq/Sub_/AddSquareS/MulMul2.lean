import Axiom.Algebra.SquareAdd.eq.Add_.AddSquareS.MulMul2
import Axiom.Algebra.Sub.eq.Add_Neg

namespace Algebra.SquareSub.eq.Sub_.AddSquareS

theorem MulMul2
  [Field α]
  {a b : α} :
-- imply
  (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
-- proof
  rw [
    Sub.eq.Add_Neg,
    SquareAdd.eq.Add_.AddSquareS.MulMul2
  ]
  simp [Sub.eq.Add_Neg]


end Algebra.SquareSub.eq.Sub_.AddSquareS

-- created on 2024-07-01
