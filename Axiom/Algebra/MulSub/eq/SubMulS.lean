import Axiom.Algebra.SubMulS.eq.MulSub


namespace Algebra.MulSub.eq

theorem SubMulS
  [Ring α]
  {x a b : α} :
-- imply
  (a - b) * x = a * x - b * x := by
-- proof
  rw [SubMulS.eq.MulSub]


end Algebra.MulSub.eq

-- created on 2024-11-26
