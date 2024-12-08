import Axiom.Basic

namespace Algebra.Sub.eq

theorem Add_Neg
  [SubNegMonoid α]
  {a b : α} :
-- imply
  a - b = a + -b := by
-- proof
  rw [sub_eq_add_neg]


end Algebra.Sub.eq

-- created on 2024-07-01
