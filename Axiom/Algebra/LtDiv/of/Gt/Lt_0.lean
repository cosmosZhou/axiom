import Axiom.Algebra.EqDivMul.of.Ne_0
import Axiom.Algebra.LtDivS.of.Gt.Lt_0
import Axiom.Algebra.Ne.of.Lt
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {n d x : α}
-- given
  (h₀ : n > x * d)
  (h₁ : d < 0) :
-- imply
  n / d < x := by
-- proof
  have := LtDivS.of.Gt.Lt_0 h₀ h₁
  have h_Ne_0 := Ne.of.Lt h₁
  rw [EqDivMul.of.Ne_0 h_Ne_0] at this
  assumption


-- created on 2025-03-30
