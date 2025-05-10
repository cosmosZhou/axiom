import Lemma.Logic.AndAndNot.is.False
open Logic


@[main]
private lemma main :
-- imply
  (q ∧ ¬p) ∧ p ↔ False := by
-- proof
  rw [And.comm (a := q)]
  apply AndAndNot.is.False


-- created on 2024-07-01
