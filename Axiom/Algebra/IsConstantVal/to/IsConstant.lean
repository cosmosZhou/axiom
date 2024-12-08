import Axiom.sympy.core.containers.vector
import Axiom.Algebra.All_Eq.to.All_EqFunS
import Axiom.Algebra.TailCons.eq.Tail
import Axiom.Algebra.All_Eq.to.IsConstant
open Mathlib

namespace Algebra.IsConstantVal.to


theorem IsConstant
  {s : Vector α n}
-- given
  (h: s.val is constant) :
-- imply
  s is constant := by
-- proof
  exact h



end Algebra.IsConstantVal.to

-- created on 2024-07-01
