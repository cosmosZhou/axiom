import Axiom.Basic

namespace Algebra.AddAdd.eq

theorem Add_Add
  [AddSemigroup α]
  {a b : α} :
-- imply
  a + b + c = a + (b + c) := by
-- proof
  rw [add_assoc]


end Algebra.AddAdd.eq

-- created on 2024-07-01
