import Axiom.sympy.core.containers.vector
import Axiom.Algebra.All_Eq_.SumMap_FunMul.DotMapS
import Axiom.Algebra.SumMap_FunMul.eq.MulSumMap
import Axiom.Algebra.SumMapVal.eq.SumMap

open Mathlib
namespace Algebra.SumMap_FunMul.eq.MulSumMap

theorem vector
  [Add β] [MulZeroClass β] [RightDistribClass β]
  {s : Vector α n}
  {f : α → β}
  {const : β} :
-- imply
  (s.map fun x => (f x) * const).sum = (s.map f).sum * const := by
-- proof
  have h : (s.val.map fun x => (f x) * const).sum = (s.val.map f).sum * const := SumMap_FunMul.eq.MulSumMap

  have h' : (s.map fun x => (f x) * const).sum = (s.val.map fun x => (f x) * const).sum := SumMapVal.eq.SumMap
  have h'' : (s.map f).sum = (s.val.map f).sum := SumMapVal.eq.SumMap
  rw [h', h'', h]


end Algebra.SumMap_FunMul.eq.MulSumMap

-- created on 2024-07-01
