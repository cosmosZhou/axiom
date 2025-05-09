import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
-- given
  (v : List α) :
-- imply
  v.substr i d = (v.drop i).take d := by
-- proof
  simp [List.substr]


-- created on 2025-05-08
