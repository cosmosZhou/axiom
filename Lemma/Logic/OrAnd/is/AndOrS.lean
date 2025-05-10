import Lemma.Logic.AndOrS.of.OrAnd
import Lemma.Logic.OrAnd.of.AndOrS
open Logic


@[main]
private lemma main:
-- imply
  p ∧ q ∨ r ↔ (p ∨ r) ∧ (q ∨ r) :=
-- proof
  ⟨AndOrS.of.OrAnd, OrAnd.of.AndOrS⟩


-- created on 2024-07-01
