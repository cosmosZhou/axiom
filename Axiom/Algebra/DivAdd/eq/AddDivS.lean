import Axiom.Algebra.AddDivS.eq.DivAdd

namespace Algebra.DivAdd.eq

theorem AddDivS
  [Field α]
  {x y a : α} :
-- imply
  (x + y) / a = x / a + y / a := by
-- proof
  rw [← AddDivS.eq.DivAdd]

end Algebra.DivAdd.eq

-- created on 2024-07-01
