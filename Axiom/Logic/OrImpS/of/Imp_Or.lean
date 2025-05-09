import Axiom.Logic.Imp.is.OrNot
import Axiom.Logic.Or_Or.is.OrOr
import Axiom.Logic.Or_Or.comm
open Logic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → (q ∨ r)) :
-- imply
  (p → q) ∨ (p → r) := by
-- proof
  rw [Imp.is.OrNot] at h
  rw [Imp.is.OrNot]
  rw [Imp.is.OrNot]
  rw [OrOr.is.Or_Or]
  rw [Or_Or.comm] at h
  apply Or.inr h


-- created on 2024-07-01
