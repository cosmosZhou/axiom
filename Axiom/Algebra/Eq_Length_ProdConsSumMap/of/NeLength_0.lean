import sympy.tensor.tensor
import Axiom.Algebra.LengthJoin.eq.SumMap_FunLength
import Axiom.Algebra.ProdCons.eq.Mul_Prod
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.MulMul.eq.Mul_Mul
open Algebra


@[main]
private lemma main
  {s : List (Tensor α shape)}
-- given
  (h : s.length ≠ 0) :
-- imply
  let head_dimension := shape.headD 1 * s.length
  let tail_dimension := s[0].shape.tail
  (head_dimension :: tail_dimension).prod = ((s.map fun t => t.args.val).flatten).length := by
-- proof
  intro head_dimension tail_dimension
  let args := (s.map fun t => t.args.val).flatten
  have h : args.length = ((s.map fun t => t.args.val).map fun t => t.length).sum :=
    LengthJoin.eq.SumMap_FunLength
  have h_eq_prod : (head_dimension :: tail_dimension).prod = head_dimension * tail_dimension.prod :=
    ProdCons.eq.Mul_Prod
  rw [h, h_eq_prod]
  simp
  have h_Eq_Fun : ((fun t => t.length) ∘ fun t : Tensor α shape => t.args.val) = fun t => t.args.val.length := by
    congr
  simp [h_Eq_Fun]
  simp [head_dimension]
  rw [Mul.comm (b := s.length)]
  rw [MulMul.eq.Mul_Mul]
  have h_tail_dimension : tail_dimension = shape.tail := by
    simp [tail_dimension]
    simp [Tensor.shape]
  have h_Eq : shape.head?.getD 1 * tail_dimension.prod = shape.prod := by
    rw [h_tail_dimension]
    cases shape <;> simp_all
  rw [h_Eq]


-- created on 2024-07-01
-- updated on 2025-05-02
