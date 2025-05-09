import Axiom.Logic.OrAnd.is.AndOrS
open Logic


@[main]
private lemma main :
-- imply
  (p ∨ r) ∧ (q ∨ r) ↔ p ∧ q ∨ r :=
-- proof
  OrAnd.is.AndOrS.symm


-- created on 2024-07-01
