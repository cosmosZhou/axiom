import Lemma.Logic.And_Or.is.OrAndS
import Lemma.Logic.AndAnd__Not.is.False
open Logic


@[main]
private lemma main
-- given
  (h : ¬p ∨ ¬q) :
-- imply
  ¬(p ∧ q) := by
-- proof
  intro hpq
  have h := And.intro hpq h
  rw [And_Or.is.OrAndS] at h
  simp [
    AndAnd__Not.is.False true,
    AndAnd__Not.is.False false
  ] at h


-- created on 2024-07-01
