import Axiom.Basic


@[main]
private lemma main
  [Mul α]
  {a b x y : α}
-- given
  (h1 : a = b)
  (h2 : x = y) :
-- imply
  a * x = b * y := by
-- proof
  rw [h1, h2]


-- created on 2024-07-01
