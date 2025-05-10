import Lemma.Logic.AndAnd.is.And_And
open Logic


@[main]
private lemma main :
-- imply
  p ∧ q ∧ r ↔ (p ∧ q) ∧ r :=
-- proof
  AndAnd.is.And_And.symm


-- created on 2024-07-01
