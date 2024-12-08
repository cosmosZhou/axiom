import Axiom.sympy.tensor.Tensor

import Axiom.Algebra.LengthJoin.eq.SumMap_FunLength
import Axiom.Algebra.ProdCons.eq.Mul_Prod
import Axiom.Algebra.Prod.eq.Mul_.HeadD.ProdTail
import Axiom.Algebra.IsConstant.to.IsConstantMap.vector
import Axiom.Algebra.MapMap.eq.Map_Comp.vector
import Axiom.Algebra.IsConstant.to.All_Eq_HeadD
import Axiom.Algebra.Ne_.Length.Zero.to.EqHeadD
import Axiom.Algebra.Ne_.Length.Zero.to.EqHeadDMap
import Axiom.Algebra.SumMap_FunMul.eq.DotMapS
import Axiom.Algebra.IsConstant.to.Eq_.Dot.Mul_.Sum.HeadD
import Axiom.Algebra.SumMapVal.eq.SumMap
import Axiom.Algebra.IsConstantVal.to.IsConstant

open Mathlib
namespace Algebra.Ne_.Length.Zero.IsConstantMap.to.Eq_.ProdConsSumMap

theorem Length
  {s : List (Tensor α)}
-- given
  (h1 : s.length ≠ 0)
  (h2: s.map (fun x => x.shape.tail) is constant) :
-- imply
  let head_dimension := (s.map fun t => t.shape.headD 1).sum
  let tail_dimension := s[0].shape.tail
  let shape := head_dimension :: tail_dimension
  let args := (s.map (fun t => t.args.val)).join
  shape.prod = args.length := by
-- proof

  let s': Vector (Tensor α) s.length := ⟨
    s,
    by simp
  ⟩

  have h2: s'.map (fun x => x.shape.tail) is constant := IsConstantVal.to.IsConstant h2

  let head_dimension := (s'.map (fun t => t.shape.headD 1)).sum
  let tail_dimension := s[0].shape.tail
  let shape := head_dimension :: tail_dimension
  let args := (s.map (fun t => t.args.val)).join

  have h_eq_map : s.map (fun t => t.args.val.length) = s.map (fun t => t.shape.prod) := by
    congr
    apply funext
    intro t
    exact t.args.property

  have h_eq_map : s.map (fun t => t.args.length) = s.map (fun t => t.shape.prod) := by
    simp [h_eq_map]

  have h_is_constant : (s'.map fun x => x.shape.tail).map (fun x => x.prod) is constant := IsConstant.to.IsConstantMap.vector h2 (fun x => x.prod)

  have h_eq_map_map : (s'.map fun x => x.shape.tail).map (fun x => x.prod) = s'.map (fun x => x.shape.tail.prod) := by
    apply MapMap.eq.Map_Comp.vector

  have h_is_constant : s'.map (fun x => x.shape.tail.prod) is constant := h_eq_map_map ▸ h_is_constant

  have h_dot : (s'.map fun t => t.shape.headD 1 * t.shape.tail.prod).sum =
    s'.map (fun t => t.shape.headD 1) ⬝ s'.map (fun t => t.shape.tail.prod) :=
    SumMap_FunMul.eq.DotMapS

  have h_eq_dot: s'.map (fun t => t.shape.headD 1) ⬝ s'.map (fun t => t.shape.tail.prod) =
    (s'.map (fun t => t.shape.headD 1)).sum * (s'.map (fun t => t.shape.tail.prod)).headD 0 :=
    IsConstant.to.Eq_.Dot.Mul_.Sum.HeadD h_is_constant 0

  have h_eq_s_0_map : (s'.map fun t => t.shape.tail.prod).headD 0 = tail_dimension.prod := Ne_.Length.Zero.to.EqHeadDMap h1

  have h_eq_dot: s'.map (fun t => t.shape.headD 1) ⬝ s'.map (fun t => t.shape.tail.prod) = head_dimension * tail_dimension.prod := by
    rw [h_eq_dot]
    rw [h_eq_s_0_map]

  have h_eq : (s'.map fun t => t.shape.headD 1 * t.shape.tail.prod).sum = head_dimension * tail_dimension.prod := by
    rw [h_dot, h_eq_dot]

  have h_eq_mul : s'.map (fun t => t.shape.prod) = s'.map (fun t => t.shape.headD 1 * t.shape.tail.prod) := by
    congr
    apply funext
    intro t
    apply Prod.eq.Mul_.HeadD.ProdTail

  have h_eq : (s'.map fun t => t.shape.prod).sum = head_dimension * tail_dimension.prod := by
    rw [h_eq_mul, h_eq]

  have h_eq : (s.map fun t => t.shape.prod).sum = head_dimension * tail_dimension.prod := by
    rw [SumMapVal.eq.SumMap.symm] at h_eq
    exact h_eq

  have h_eq : (s.map fun t => t.args.length).sum = head_dimension * tail_dimension.prod := by
    rw [h_eq_map, h_eq]

  have h_eq_map_map : (s.map (fun t => t.args.val)).map (fun s => s.length) = s.map fun t => t.args.length := by
    simp only [MapMap.eq.Map_Comp]
    simp
    -- apply congr_arg
    -- rfl

  have h_eq : ((s.map fun t => t.args.val).map fun s => s.length).sum = head_dimension * tail_dimension.prod := by
    rw [h_eq_map_map, h_eq]

  have h_eq_prod : shape.prod = head_dimension * tail_dimension.prod := ProdCons.eq.Mul_Prod

  have h : args.length = ((s.map fun t => t.args.val).map fun s => s.length).sum := LengthJoin.eq.SumMap_FunLength
  have h : shape.prod = args.length := by
    rw [h_eq_prod, h_eq.symm, h]

  exact h

end Algebra.Ne_.Length.Zero.IsConstantMap.to.Eq_.ProdConsSumMap

-- created on 2024-07-01
