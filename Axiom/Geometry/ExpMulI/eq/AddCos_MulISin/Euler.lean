import Axiom.Geometry.ExpMulI.eq.AddCos_MulISin.Euler.complex
open Geometry


@[main]
private lemma main
  {x : ℝ} :
-- imply
  (I * x).exp = cos x + I * sin x := by
-- proof
  have h_cos : cos x = (x : ℂ).cos := by simp
  have h_sin : sin x = (x : ℂ).sin := by simp
  rw [h_cos, h_sin]
  exact ExpMulI.eq.AddCos_MulISin.Euler.complex (x := x)


-- created on 2025-01-05
