import Axiom.Basic

namespace Algebra.SquareAdd.eq.Add_.AddSquareS

theorem MulMul2
  [CommSemiring α]
  {a b : α} :
-- imply
  (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
-- proof
  apply add_sq'

end Algebra.SquareAdd.eq.Add_.AddSquareS

-- created on 2024-07-01
