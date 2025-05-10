import Lemma.Basic


@[main]
private lemma left
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {b c : α}
-- given
  (h : b < c)
  (a : α) :
-- imply
  a + b < a + c :=
-- proof
  add_lt_add_left h a


@[main]
private lemma main
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {b c : α}
-- given
  (h : b < c)
  (a : α) :
-- imply
  b + a < c + a :=
-- proof
  add_lt_add_right h a


-- created on 2024-07-01
-- updated on 2025-04-04
