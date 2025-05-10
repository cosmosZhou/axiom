import Lemma.Logic.And_Or.of.OrAndS
import Lemma.Logic.OrAndS.of.And_Or
open Logic


@[main]
private lemma main :
-- imply
  p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r :=
-- proof
  ⟨OrAndS.of.And_Or, And_Or.of.OrAndS⟩


-- created on 2024-07-01
