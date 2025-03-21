import Axiom.Basic


@[main]
private lemma main
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α} :
-- imply
  b - a > 0 ↔ a < b :=
-- proof
  sub_pos


-- created on 2024-11-25
