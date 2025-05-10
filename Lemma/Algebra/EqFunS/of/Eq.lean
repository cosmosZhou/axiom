import Lemma.Basic


@[main]
private lemma main
  {f : α → β}
  {a b : α}
-- given
  (h : a = b) :
-- imply
  f a = f b := by
-- proof
  rw [h]


-- created on 2025-04-27
