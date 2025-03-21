import Axiom.Algebra.ExpAdd.eq.MulExpS
import Axiom.Algebra.Mul_Div.eq.DivMul.comm
import Axiom.Algebra.MulMul.eq.Mul_Mul
import Axiom.Algebra.AddDivS.eq.DivAdd
open Algebra


@[main]
private lemma main
  {x : ℂ} :
-- imply
  (I * x).exp = x.cos + I * x.sin := by
-- proof
  rw [Complex.sin, Complex.cos]
  rw [Mul_Div.eq.DivMul.comm]
  rw [MulMul.eq.Mul_Mul]
  simp
  rw [AddDivS.eq.DivAdd]
  simp
  rw [Mul.comm]


-- created on 2025-01-05
