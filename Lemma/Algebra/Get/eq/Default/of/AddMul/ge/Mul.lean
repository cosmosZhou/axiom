import stdlib.List.Vector
import Lemma.Algebra.OrGeS.of.AddMul.ge.Mul
open Algebra


@[main]
private lemma main
  [Inhabited α]
  {i j : ℕ}
-- given
  (h : i * n + j ≥ m * n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  v[i, j] = default := by
-- proof
  simp [GetElem.getElem]
  have := OrGeS.of.AddMul.ge.Mul h
  cases' this with hi hj
  ·
    split_ifs with h
    ·
      linarith
    ·
      intro hj
      simp [Inhabited.default]
  ·
    intro hj'
    linarith


-- created on 2025-05-09
