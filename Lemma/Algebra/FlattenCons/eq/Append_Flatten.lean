import Lemma.Basic


@[main]
private lemma main
-- given
  (head : List α)
  (tail : List (List α)) :
-- imply
  (head :: tail).flatten = head ++ tail.flatten := by
-- proof
  induction tail with
  | nil =>
    simp [List.flatten]
  | cons x xs ih =>
    simp [List.flatten, List.append_assoc, ih]


-- created on 2025-05-08
