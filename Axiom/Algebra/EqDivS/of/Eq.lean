import Axiom.Basic


@[main]
private lemma main
  [Div α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  x / d = y / d := by
-- proof
  rw [h]


-- created on 2024-07-01
