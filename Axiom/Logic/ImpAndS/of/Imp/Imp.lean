import Axiom.Logic.Imp_And.of.Imp.Imp
import Axiom.Logic.Imp.of.Imp.Imp
open Logic


@[main]
private lemma main
-- given
  (h₀ : p0 → q0)
  (h₁ : p1 → q1) :
-- imply
  p0 ∧ p1 → q0 ∧ q1 := by
-- proof
  apply Imp_And.of.Imp.Imp
  ·
    have : p0 ∧ p1 → p0 := by tauto
    exact Imp.of.Imp.Imp this h₀
  ·
    have : p0 ∧ p1 → p1 := by tauto
    exact Imp.of.Imp.Imp this h₁


-- created on 2025-04-10
