import Lemma.Logic.And_Not.of.NotImp
import Lemma.Logic.NotImp.of.And_Not
open Logic


@[main]
private lemma main :
-- imply
  ¬(p → q) ↔ p ∧ ¬q :=
-- proof
  ⟨And_Not.of.NotImp, NotImp.of.And_Not⟩


-- created on 2024-07-01
