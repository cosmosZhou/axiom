import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
-- given
  (v : List α)
  (n : ℕ) :
-- imply
  v.take n ++ v.drop n = v := by
-- proof
  induction v with
  | nil =>
    simp [List.take, List.drop]
  | cons x xs ih =>
    match n with
    | .zero =>
      simp [List.take, List.drop]
    | .succ n =>
      simp [List.take, List.drop, ih]


-- created on 2025-05-09
