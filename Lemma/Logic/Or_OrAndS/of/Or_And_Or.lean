import Lemma.Logic.OrAndS.is.And_Or
open Logic


@[main]
private lemma main
-- given
  (h : t ∨ p ∧ (q ∨ r)) :
-- imply
  t ∨ p ∧ q ∨ p ∧ r := by
-- proof
  simp [OrAndS.is.And_Or.left]
  assumption


-- created on 2025-04-21
