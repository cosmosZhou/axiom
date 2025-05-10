import sympy.core.power
import Lemma.Algebra.SubSquare_MulMul4.le.Zero.of.Ge_0.AddAddMul_Square.ge.Zero
open Algebra


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : ∀ x : ℝ, a * x² + b * x + c ≥ 0)
  (h₁ : a ≥ 0) :
-- imply
  b² ≤ 4 * a * c := by
-- proof
  have := SubSquare_MulMul4.le.Zero.of.Ge_0.AddAddMul_Square.ge.Zero h₀ h₁
  simp_all


-- created on 2025-04-06
