import Axiom.Algebra.AddAdd.eq.Add_Add

namespace Algebra.Add_Add.eq

theorem AddAdd
  [AddSemigroup α]
  {a b : α} :
-- imply
  a + (b + c) = a + b + c := by
-- proof
  rw [AddAdd.eq.Add_Add]


end Algebra.Add_Add.eq

-- created on 2024-07-01
