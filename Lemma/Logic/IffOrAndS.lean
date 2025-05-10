import Lemma.Logic.OrAndS.is.And_Or
import Lemma.Logic.Or_Not.law_of_excluded_middle
open Logic


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∧ q ∨ p ∧ ¬q ↔ p := by
-- proof
  simp [OrAndS.is.And_Or.left]
  simp [Or_Not.law_of_excluded_middle]


-- created on 2025-04-09
-- updated on 2025-04-21
