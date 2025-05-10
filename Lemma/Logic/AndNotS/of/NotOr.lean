import Lemma.Logic.NotAnd.is.OrNotS
open Logic


@[main]
private lemma main
-- given
  (h : ¬(p ∨ q)) :
-- imply
  ¬p ∧ ¬q := by
-- proof
  by_contra h_And
  rw [NotAnd.is.OrNotS] at h_And
  simp at h_And
  contradiction


-- created on 2024-07-01
