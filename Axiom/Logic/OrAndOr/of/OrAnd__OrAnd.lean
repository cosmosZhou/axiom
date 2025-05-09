import Axiom.Logic.Or_Or.is.OrOr
import Axiom.Logic.OrAndS.is.AndOr
open Logic


@[main]
private lemma main
-- given
  (h : (p ∧ c) ∨ (q ∧ c) ∨ r) :
-- imply
  (p ∨ q) ∧ c ∨ r := by
-- proof
  rw [Or_Or.is.OrOr] at h
  simp only [OrAndS.is.AndOr true] at h
  assumption


-- created on 2025-04-07
-- updated on 2025-04-08
