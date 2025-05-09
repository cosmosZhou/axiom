import sympy.tensor.tensor
import Axiom.Tensor.Mul.eq.Prod
import Axiom.Algebra.ZipWithHMul.eq.Replicate_0.of.Le
import Axiom.Algebra.Le.of.Eq
open Tensor Algebra


@[main]
private lemma main
  [MulZeroClass α]
  {a : Tensor α s} :
-- imply
  Zeros s * a = Zeros s := by
-- proof
  rw [Mul.eq.Prod]
  congr
  simp [Zeros]
  have h_Eq : s.prod = a.args.val.length := by simp
  have h_Le := Le.of.Eq h_Eq
  rw [ZipWithHMul.eq.Replicate_0.of.Le h_Le]


-- created on 2025-05-02
