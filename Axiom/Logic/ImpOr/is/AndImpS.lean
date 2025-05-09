import Axiom.Logic.Imp.is.OrNot
import Axiom.Logic.And_Or.is.OrAndS
import Axiom.Logic.AndOr.is.OrAndS
import Axiom.Logic.OrOr.is.Or_Or
import Axiom.Logic.OrAnd.is.AndOrS
import Axiom.Logic.OrAndS.is.AndOr
import Axiom.Logic.Or_Or.is.OrOr
import Axiom.Logic.IffAndOr
open Logic


@[main]
private lemma main :
-- imply
  (p ∨ q) → r ↔ (p → r) ∧ (q → r)  := by
-- proof
  rw [Imp.is.OrNot]
  rw [Imp.is.OrNot]
  rw [Imp.is.OrNot]
  rw [And_Or.is.OrAndS]
  simp
  rw [AndOr.is.OrAndS]
  rw [AndOr.is.OrAndS]
  simp
  rw [OrOr.is.Or_Or]
  rw [OrAnd.is.AndOrS (q := r)]
  simp [OrAndS.is.AndOr false]
  rw [Or_Or.is.OrOr]
  simp [IffAndOr true]


-- created on 2024-07-01
