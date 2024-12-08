import Axiom.Basic

namespace Algebra.Sub_Add.eq

theorem SubSub
  [SubtractionCommMonoid α]
  {a b c : α} :
-- imply
  a - (b + c) = a - b - c := by
-- proof
  rw [sub_add_eq_sub_sub]


end Algebra.Sub_Add.eq

-- created on 2024-07-01
