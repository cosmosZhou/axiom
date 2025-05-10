import Lemma.Logic.OrAnd.of.AndOrS
open Logic


@[main]
private lemma main
-- given
  (h : (p ∨ r) ∧ (q ∨ r)) :
-- imply
   r ∨ p ∧ q := by
-- proof
  rw [Or.comm]
  apply OrAnd.of.AndOrS h


-- created on 2025-04-05
