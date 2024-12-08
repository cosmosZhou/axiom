import Axiom.sympy.core.containers.vector
import Axiom.Algebra.IsConstant.to.IsConstantMap

open Mathlib

namespace Algebra.IsConstant.to.IsConstantMap

theorem vector
  {s : Vector α n}
-- given
  (h: s is constant)
  (f : α → β) :
-- imply
  s.map f is constant := by
-- proof
  apply IsConstant.to.IsConstantMap h


end Algebra.IsConstant.to.IsConstantMap

-- created on 2024-07-01
