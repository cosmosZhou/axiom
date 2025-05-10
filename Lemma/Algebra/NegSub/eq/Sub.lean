import Lemma.Basic


@[main]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  -(b - a) = a - b := by
-- proof
  simp


-- created on 2024-11-29
-- updated on 2025-03-16
