import Axiom.sympy.core.containers.vector
import Axiom.Algebra.SumCons.eq.Add_Sum
import Axiom.Algebra.SumMap_FunMul.eq.DotMapS
import Axiom.Algebra.Map_Id.simp
import Axiom.Algebra.Map.eq.Replicate
import Axiom.Algebra.IsConstant.to.Eq_Replicate_HeadD.vector
import Axiom.Algebra.SumMap_FunMul.eq.MulSumMap.vector

open Mathlib
namespace Algebra.IsConstant.to.Eq_.Dot.Mul_.Sum

theorem HeadD
  [Add α] [MulZeroClass α] [RightDistribClass α]
  {s s' : Vector α n}
-- given
  (h: s is constant)
  (default : α) :
-- imply
  s' ⬝ s = s'.sum * s.headD default := by
-- proof
  have h_eq_sum : (s'.map fun x => x * s.headD default).sum = (s'.map fun x => x) ⬝ (s'.map fun _ => s.headD default) := by
    apply SumMap_FunMul.eq.DotMapS

  have h_eq := IsConstant.to.Eq_Replicate_HeadD.vector h default

  simp at h_eq_sum
  rw [
    Map.eq.Replicate,
    h_eq.symm
  ] at h_eq_sum

  have h_eq : (s'.map fun x ↦ x * s.headD default).sum =
    (s'.map fun x => x).sum * s.headD default :=
    SumMap_FunMul.eq.MulSumMap.vector

  simp at h_eq

  rw [h_eq_sum.symm, h_eq]


end Algebra.IsConstant.to.Eq_.Dot.Mul_.Sum

-- created on 2024-07-01
