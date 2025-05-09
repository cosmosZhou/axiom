import Axiom.Logic.And_NotAnd_Not.is.OrAndS
open Logic


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∧ ¬(q ∧ ¬p) ↔ p := by
-- proof
  rw [And_NotAnd_Not.is.OrAndS]
  tauto


-- created on 2025-04-09
