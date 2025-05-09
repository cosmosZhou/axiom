import Axiom.Algebra.LeMulS.of.Le.Gt_0
import Axiom.Algebra.Ne.of.Gt
import Axiom.Algebra.EqMulDiv.of.Ne_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a b : α}
-- given
  (h₀ : a / x ≤ b / x)
  (h₁ : x > 0) :
-- imply
  a ≤ b := by
-- proof
  have := LeMulS.of.Le.Gt_0 h₀ h₁
  have h₁ := Ne.of.Gt h₁
  rw [EqMulDiv.of.Ne_0 h₁ a] at this
  rw [EqMulDiv.of.Ne_0 h₁ b] at this
  assumption


-- created on 2025-03-30
