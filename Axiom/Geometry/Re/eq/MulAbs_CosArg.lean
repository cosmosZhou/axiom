import Axiom.Algebra.Expr.eq.AddRe_MulIIm
import Axiom.Algebra.EqMulS.of.Eq
import Axiom.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  {z : ℂ} :
-- imply
  re z = abs z * cos (arg z) := by
-- proof
  by_cases h_Ne_0 : z ≠ 0
  have h := Complex.cos_arg h_Ne_0
  have h := EqMulS.of.Eq h (abs z)
  simp [h_Ne_0] at h
  rw [Mul.comm] at h
  exact h.symm
  simp [h_Ne_0]


-- created on 2025-01-13
