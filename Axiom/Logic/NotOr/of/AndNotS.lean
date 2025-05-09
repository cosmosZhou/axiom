import Axiom.Logic.OrAndS.of.And_Or
import Axiom.Logic.AndAnd_Not.is.False
import Axiom.Logic.AndAndNot.is.False
open Logic


@[main]
private lemma main
-- given
  (h : ¬p ∧ ¬q) :
-- imply
  ¬(p ∨ q) := by
-- proof
  by_contra h_Or
  have h := And.intro h h_Or
  have h := OrAndS.of.And_Or h
  simp [AndAnd_Not.is.False, AndAndNot.is.False] at h


-- created on 2024-07-01
-- updated on 2025-04-05
