import Axiom.Algebra.SumCons.eq.Add_Sum
import Axiom.Algebra.SumMap_FunMul.eq.DotMapS
import Axiom.Algebra.EqMap_Id
import Axiom.Algebra.Map.eq.Replicate
import Axiom.Algebra.Eq_Replicate_HeadD.of.IsConstant.vector
import Axiom.Algebra.SumMap_FunMul.eq.MulSumMap.vector
open Algebra


@[main]
private lemma main
  [Add α] [MulZeroClass α] [RightDistribClass α]
  {s s' : Vector α n}
-- given
  (h: s is constant)
  (default : α) :
-- imply
  s' ⬝ s = s'.sum * s.headD default := by
-- proof
  have h_eq_sum := SumMap_FunMul.eq.DotMapS
    (s := s')
    (f₁ := id)
    (f₂ := fun _ => s.headD default)
  have h_eq := Eq_Replicate_HeadD.of.IsConstant.vector h default
  simp at h_eq_sum
  rw [
    Map.eq.Replicate,
    h_eq.symm
  ] at h_eq_sum
  have h_eq := SumMap_FunMul.eq.MulSumMap.vector
    (s := s')
    (f := id)
    (const := s.headD default)
  simp at h_eq
  rw [h_eq_sum.symm, h_eq]


-- created on 2024-07-01
