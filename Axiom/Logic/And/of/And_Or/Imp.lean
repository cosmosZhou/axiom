import sympy.core.logic
import Axiom.Basic


@[main]
private lemma left
-- given
  (h₀ : p → q)
  (h₁ : r' ∧ (p ∨ r)) :
-- imply
  r' ∧ (q ∨ r) := by
-- proof
  mpr [h₀]
  assumption


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : r' ∧ (r ∨ p)) :
-- imply
  r' ∧ (r ∨ q) := by
-- proof
  mp [h₀] at h₁
  assumption


-- created on 2025-04-12
-- updated on 2025-04-13
