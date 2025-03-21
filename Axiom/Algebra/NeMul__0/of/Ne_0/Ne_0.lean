import Axiom.Basic


@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
-- imply
   a * b ≠ 0 := by
-- proof
  simp [h0, h1]


-- created on 2024-07-01
