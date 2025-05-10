import Lemma.Logic.OrNot.of.Imp
import Lemma.Logic.Imp.of.OrNot
open Logic


@[main]
private lemma main :
-- imply
  (p → q ↔ ¬p ∨ q)  :=
-- proof
  ⟨OrNot.of.Imp, Imp.of.OrNot⟩


-- created on 2024-07-01
