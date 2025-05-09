import Axiom.Logic.Imp.is.OrNot
import Axiom.Logic.NotAnd.is.OrNotS
import Axiom.Logic.OrOr.is.Or_Or
open Logic


@[main]
private lemma main :
-- imply
  p → q → r ↔ p ∧ q → r := by
-- proof
  rw [
    Imp.is.OrNot,
    Imp.is.OrNot,
    Imp.is.OrNot,
    NotAnd.is.OrNotS,
    OrOr.is.Or_Or
  ]


-- created on 2024-07-01
