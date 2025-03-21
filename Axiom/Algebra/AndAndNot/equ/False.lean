import Axiom.Algebra.AndAnd__Not.equ.False
import Axiom.Algebra.Iff_Not.of.Iff_Not
import Axiom.Algebra.Imply.of.Cond
open Algebra


@[simp, main]
private lemma main :
-- imply
  (¬p ∧ q) ∧ p ↔ False := by
-- proof
  let p' := ¬p
  have h := Iff_Not.of.Iff_Not (by rfl : p' ↔ ¬p)
  rw [h]
  simp
  apply Imply.of.Cond


-- created on 2024-07-01
