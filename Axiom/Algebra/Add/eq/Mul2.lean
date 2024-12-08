import Axiom.Basic

namespace Algebra.Add.eq

@[simp]
theorem Mul2
  [NonAssocSemiring α]
  {a : α} :
-- imply
  a + a = 2 * a := by
-- proof
  rw [two_mul]


end Algebra.Add.eq

-- created on 2024-07-01
