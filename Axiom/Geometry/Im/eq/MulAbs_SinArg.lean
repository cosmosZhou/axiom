import Axiom.Algebra.EqMulS.of.Eq
import Axiom.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  {z : ℂ} :
-- imply
  im z = abs z * sin (arg z) := by
-- proof
  have h := Complex.sin_arg z
  have h := EqMulS.of.Eq h (abs z)
  by_cases h_Ne_0 : z ≠ 0
  simp [h_Ne_0] at h
  rw [Mul.comm] at h
  exact h.symm
  simp [h_Ne_0]


-- created on 2025-01-13
