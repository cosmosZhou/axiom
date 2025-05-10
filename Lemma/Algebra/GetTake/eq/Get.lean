import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Inhabited α]
-- given
  (v : List.Vector α N)
  (j : Fin n) :
-- imply
  (v.take n)[j] = v[j] := by
-- proof
  simp [GetElem.getElem]
  split_ifs with h
  .
    simp [List.Vector.take]
    cases v
    simp
    simp [List.Vector.get]
  .
    rfl


-- created on 2025-05-09
