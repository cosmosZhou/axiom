import Axiom.Logic.AndAnd__Not.is.False
import Axiom.Logic.Iff_Not.of.Iff_Not
import Axiom.Logic.Imp.of.Cond
open Logic


@[main]
private lemma main :
-- imply
  (¬p ∧ q) ∧ p ↔ False := by
-- proof
  let p' := ¬p
  have h := Iff_Not.of.Iff_Not (by rfl : p' ↔ ¬p)
  rw [h]
  simp
  apply Imp.of.Cond


-- created on 2024-07-01
