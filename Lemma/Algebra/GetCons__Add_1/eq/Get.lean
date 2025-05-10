import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Inhabited α]
-- given
  (head : List.Vector α n)
  (tail : List.Vector (List.Vector α n) m)
  (i : ℕ) :
-- imply
  (head ::ᵥ tail)[i + 1] = tail[i] := by
-- proof
  simp [GetElem.getElem]
  split_ifs with h
  ·
    simp [List.Vector.cons]
    let ⟨tail, _⟩ := tail
    simp [List.Vector.get]
  ·
    simp


-- created on 2025-05-08
