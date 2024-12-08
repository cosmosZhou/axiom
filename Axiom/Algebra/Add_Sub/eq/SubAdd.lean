import Axiom.Basic

namespace Algebra.Add_Sub.eq

theorem SubAdd
  [SubNegMonoid α]
  {a b c : α} :
-- imply
  a + (b - c) = a + b - c := by
-- proof
  rw [add_sub_assoc]


end Algebra.Add_Sub.eq

-- created on 2024-07-01
