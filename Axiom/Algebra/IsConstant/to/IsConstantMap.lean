import Axiom.Algebra.All_Eq.to.All_EqFunS
import Axiom.sympy.core.containers.list

namespace Algebra.IsConstant.to

theorem IsConstantMap
  {s : List α}
-- given
  (h: s is constant)
  (f : α → β) :
-- imply
  s.map f is constant := by
-- proof
  induction s with
  | nil =>
    -- Base case: s = []
    simp [IsConstant.is_constant]
  | cons x s _ =>
    simp [IsConstant.is_constant]

    exact All_Eq.to.All_EqFunS h

end Algebra.IsConstant.to

-- created on 2024-07-01
