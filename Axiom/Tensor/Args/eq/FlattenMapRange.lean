import sympy.sets.sets
import sympy.tensor.tensor
import Axiom.Algebra.EqAdd_Mul_DivSub1Sign_2
import Axiom.Algebra.NotLe
open Algebra


@[main]
private lemma main
  [Inhabited α]
-- given
  (t : Tensor α (s₀ :: s))
  (h : s₀ > 0) :
-- imply
  t.args = ((List.Vector.range s₀).map fun i => t[i].args).flatten := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.getElem]
  simp [EqAdd_Mul_DivSub1Sign_2]
  have : t.length = s₀ := by simp [Tensor.length]
  simp [this]
  norm_cast
  simp [NotLe]
  simp [Tensor.toVector, h]
  have : t.args.length / s₀ = s.prod := by
    simp
    sorry
  simp [this]
  sorry


-- created on 2025-05-06
