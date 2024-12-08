import Axiom.Basic

namespace Algebra.NegSub.eq

@[simp]
theorem Sub
  [AddGroup α]
  -- [Neg α]
  {a b : α} :
-- imply
  -(b - a) = a - b := by
-- proof
  simp


end Algebra.NegSub.eq

-- created on 2024-11-29
