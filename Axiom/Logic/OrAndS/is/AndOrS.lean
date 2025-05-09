import Axiom.Logic.AndNotS.is.NotOr
import Axiom.Logic.Or_Not.is.Imp
import Axiom.Logic.OrNot.is.Imp
import Axiom.Logic.ImpOr.is.AndImpS
open Logic


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∧ q ∨ ¬p ∧ ¬q ↔ (¬p ∨ q) ∧ (p ∨ ¬q) := by
-- proof
  rw [AndNotS.is.NotOr]
  rw [Or_Not.is.Imp]
  rw [Or_Not.is.Imp]
  rw [OrNot.is.Imp]
  rw [ImpOr.is.AndImpS]
  tauto


-- created on 2025-04-18
