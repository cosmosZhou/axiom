import Axiom.sympy.core.containers.vector
import Axiom.Algebra.All_Eq_.SumMap_FunMul.DotMapS
import Axiom.Algebra.SumMap_FunMul.eq.MulSumMap

open Mathlib
namespace Algebra.SumMapVal.eq

@[simp]
theorem SumMap
  [Add β] [Zero β]
  {s : Vector α n}
  {f : α → β} :
-- imply
  (s.val.map f).sum = (s.map f).sum := by
-- proof
  rfl


end Algebra.SumMapVal.eq

-- created on 2024-07-01
