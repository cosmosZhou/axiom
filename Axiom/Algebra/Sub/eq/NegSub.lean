import Axiom.Algebra.NegSub.eq.Sub

namespace Algebra.Sub.eq

theorem NegSub
  [AddGroup α]
  -- [Neg α]
  {a b : α} :
-- imply
  a - b = -(b - a) := by
-- proof
  rw [NegSub.eq.Sub]



end Algebra.Sub.eq

-- created on 2024-11-29
