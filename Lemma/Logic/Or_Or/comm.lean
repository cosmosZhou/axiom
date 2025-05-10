import Lemma.Logic.Or_Or.is.OrOr
open Logic


@[main]
private lemma main :
-- imply
  a ∨ b ∨ c ↔ b ∨ a ∨ c := by
-- proof
  rw [Or_Or.is.OrOr]
  rw [Or.comm (b := b)]
  rw [OrOr.is.Or_Or]


-- created on 2024-07-01
