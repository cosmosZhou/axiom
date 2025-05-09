import Axiom.Algebra.SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0
import Axiom.Algebra.SubMulS.eq.Mul_Sub
open Algebra


@[main]
private lemma main
  [Field α]
  {x a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  x / a - x / b = x * (b - a) / (a * b) := by
-- proof
  have := SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0 (x := x) (y := x) h₀ h₁
  rw [SubMulS.eq.Mul_Sub] at this
  assumption


-- created on 2025-04-06
