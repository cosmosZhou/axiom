import stdlib.Slice
import Axiom.Basic


@[main]
private lemma main
  {s : List α} :
-- imply
  (s.drop i).drop j = s.drop (i + j) := by
-- proof
  simp


-- created on 2025-05-05
