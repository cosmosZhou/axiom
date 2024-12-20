import Axiom.sympy.core.containers.list

import Axiom.Algebra.Gt_.Length.Zero.Gt_0.to.Eq_.ProdTail.DivProd
import Axiom.Algebra.Gt_.Length.Zero.Gt_0.to.Eq_.Prod.Mul_ProdTail
import Axiom.Algebra.Lt.to.Le_.AddMul.Mul
import Axiom.Algebra.Le_.Add.Length.to.EqLengthSubstr

open Mathlib Algebra

-- the concept of a tensor is a generalization of a matrix, like the tensor concept in pytorch / tensorflow
structure Tensor (α : Type _) where
  shape : List ℕ
  args : Vector α shape.prod


-- Define the Inhabited instance for Tensor
instance (α : Type _) : Inhabited (Tensor α) where
  default := ⟨[0], [], rfl⟩



def Tensor.ToList (t : Tensor α) : List (Tensor α) :=
  if h1 : t.shape.length > 0 then
    if h2 : t.shape[0] > 0 then
      let shape := t.shape
      let args := t.args.val

      let m := shape[0] -- the number of rows

      let n := args.length / m -- the number of columns

      have h_precondition : shape.prod = args.length := by rw [t.args.property]

      have h_eq_prod_tail := Gt_.Length.Zero.Gt_0.to.Eq_.ProdTail.DivProd h1 h2

      have h_eq_prod_tail : shape.tail.prod = args.length / m := h_precondition ▸ h_eq_prod_tail

      have h_eq_prod_tail : shape.tail.prod = n := by rw [h_eq_prod_tail]

      have h_eq_mul := Gt_.Length.Zero.Gt_0.to.Eq_.Prod.Mul_ProdTail h1 h2

      have h_eq_mul : args.length = m * n := by
        rw [h_precondition, h_eq_prod_tail] at h_eq_mul
        exact h_eq_mul

      List.arange m |>.map λ i : Fin m => -- iterate over the slices
        have h_lt : i < m := by simp

        have h_le := Lt.to.Le_.AddMul.Mul h_lt n

        have h_le : i * n + n ≤ args.length := h_eq_mul.symm ▸ h_le

        ⟨
          shape.tail,
          ⟨
            args.substr (i * n) n,
            by rw [
              h_eq_prod_tail,
              Le_.Add.Length.to.EqLengthSubstr h_le
            ]
          ⟩
        ⟩
    else
      []
  else
    []
