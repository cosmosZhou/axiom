import Axiom.Algebra.DivMul.eq.MulDiv

namespace Algebra.MulDiv.eq

theorem DivMul
  [DivisionCommMonoid α]
  {a b c : α} :
-- imply
  a / c * b = a * b / c := by
-- proof
  rw [DivMul.eq.MulDiv]


end Algebra.MulDiv.eq

-- created on 2024-07-01
