import Axiom.Algebra.Sub.eq.Add_Neg

namespace Algebra.Add_Neg.eq

theorem Sub
  [SubNegMonoid α]
  {a b : α} :
-- imply
  a + -b = a - b := by
-- proof
  rw [Sub.eq.Add_Neg]


end Algebra.Add_Neg.eq

-- created on 2024-07-01
