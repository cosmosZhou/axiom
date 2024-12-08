import Axiom.sympy.core.containers.vector
import Axiom.Algebra.All_Eq_.SumMap_FunMul.DotMapS

open Mathlib
namespace Algebra.SumMap_FunMul.eq

theorem DotMapS
  [Add β] [Zero β] [Mul β]
  {s : Vector α n}
  {f₁ f₂ : α → β} :
-- imply
  (s.map fun x => (f₁ x) * (f₂ x)).sum = (s.map f₁) ⬝ (s.map f₂) :=
-- proof
  All_Eq_.SumMap_FunMul.DotMapS


end Algebra.SumMap_FunMul.eq

-- created on 2024-07-01
