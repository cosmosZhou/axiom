import Axiom.sympy.core.containers.list
import Axiom.Algebra.All_Eq.to.All_EqFunS
import Axiom.Algebra.TailCons.eq.Tail
import Axiom.Algebra.All_Eq.to.IsConstant

namespace Algebra.IsConstant.to

theorem IsConstantTail
  {s : List α}
-- given
  (h: s is constant) :
-- imply
  s.tail is constant := by
-- proof
  cases s with
  | nil =>
    simp [IsConstant.is_constant]
  | cons x0 X =>
    simp [IsConstant.is_constant] at h
    simp [TailCons.eq.Tail]
    apply All_Eq.to.IsConstant h


end Algebra.IsConstant.to

-- created on 2024-07-01
