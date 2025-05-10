import Lemma.Basic


@[main]
private lemma left
  [Add α] [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {b c : α}
-- given
  (h : b ≤ c)
  (a : α) :
-- imply
  a + b ≤ a + c :=
-- proof
  add_le_add_left h a


@[main]
private lemma main
  [Add α] [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {b c : α}
-- given
  (h : b ≤ c)
  (a : α) :
-- imply
  b + a ≤ c + a :=
-- proof
  add_le_add_right h a


-- created on 2024-07-01
-- updated on 2025-03-15
