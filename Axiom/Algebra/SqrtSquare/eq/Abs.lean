import Axiom.Basic


@[simp, main]
private lemma main
  {x : ℝ} :
-- imply
  √x² = |x| := by
-- proof
  simp [Root.sqrt]
  rw [Real.sqrt_sq_eq_abs]


-- created on 2025-01-16
