import Axiom.Basic


@[simp, main]
private lemma main
  [AddGroup α]
  {a : α} :
-- imply
  a - a = 0 := by
-- proof
  rw [sub_self]


-- created on 2024-07-01
