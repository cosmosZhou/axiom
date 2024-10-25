import Mathlib.Tactic
import Axiom.sympy.core.containers.list

import Axiom.algebra.gt_zero.gt_zero.then.eq.prod.tail
import Axiom.algebra.gt_zero.gt_zero.then.eq_prod.mul.prod.tail
import Axiom.algebra.lt.then.add_le.mul
import Axiom.algebra.le_length.then.eq.length.substr


-- the concept of a tensor is a generalization of a matrix, like the tensor concept in pytorch / tensorflow
structure Tensor (α : Type _) where
  shape : List ℕ
  args : List α
  precondition : shape.prod = args.length


-- Define the Inhabited instance for Tensor
instance (α : Type _) : Inhabited (Tensor α) where
  default := ⟨[0], [], rfl⟩


def Tensor.ToList (t : Tensor α) : List (Tensor α) :=
  if h1 : t.shape.length > 0 then
    if h2 : t.shape[0] > 0 then
      let shape := t.shape
      let args := t.args

      let m := shape[0] -- the number of rows

      let n := args.length / m -- the number of columns

      have h_precondition : shape.prod = args.length := by rw [t.precondition]

      have h_eq_prod_tail := algebra.gt_zero.gt_zero.then.eq.prod.tail h1 h2

      have h_eq_prod_tail : shape.tail.prod = args.length / m := by
        rw [h_precondition] at h_eq_prod_tail
        exact h_eq_prod_tail

      have h_eq_prod_tail : shape.tail.prod = n := by rw [h_eq_prod_tail]

      have h_eq_mul := algebra.gt_zero.gt_zero.then.eq_prod.mul.prod.tail h1 h2

      have h_eq_mul : args.length = m * n := by
        rw [h_precondition, h_eq_prod_tail] at h_eq_mul
        exact h_eq_mul

      List.arange m |>.map λ i : Fin m => -- iterate over the slices
        have h_lt : i < m := by simp

        have h_le := algebra.lt.then.add_le.mul h_lt n

        have h_le : i * n + n ≤ args.length := by
          rw [h_eq_mul.symm] at h_le
          exact h_le

        let argsᵢ := args.substr (i * n) n
        have h_eq_prod_tail_i : shape.tail.prod = argsᵢ.length := by rw [
          h_eq_prod_tail,
          algebra.le_length.then.eq.length.substr h_le
        ]

        ⟨shape.tail, argsᵢ, h_eq_prod_tail_i⟩
    else
      []
  else
    []
