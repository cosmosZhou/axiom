import Axiom.Basic

namespace Algebra.Eq.to.Eq

theorem reverse
  {a b : α}
-- given
  (h : a = b) :
-- imply
  b = a := by
-- proof
  apply Eq.symm h


end Algebra.Eq.to.Eq

-- created on 2024-07-01
