import Lemma.Logic.OrAnd.is.AndOrS
open Logic


@[main]
private lemma main :
-- imply
  r ∨ p ∧ q ↔ (r ∨ p) ∧ (r ∨ q) := by
-- proof
  rw [
    Or.comm,
    Or.comm (a := r),
    Or.comm (a := r)
  ]
  apply OrAnd.is.AndOrS


-- created on 2024-07-01
