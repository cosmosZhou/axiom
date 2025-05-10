import Lemma.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : ¬a > b) :
-- imply
  a ≤ b := by
-- proof
  apply not_lt.mp h


-- created on 2025-03-23
