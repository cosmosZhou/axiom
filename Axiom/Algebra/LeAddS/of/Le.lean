import Axiom.Basic


@[main]
private lemma main
  [Add α] [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {b c : α}
-- given
  (h : b ≤ c)
  (a : α)
  (left : Bool := false) :
-- imply
  match left with
  | true =>
    a + b ≤ a + c
  | false =>
    b + a ≤ c + a :=
-- proof
  match left with
  | true => 
    add_le_add_left h a
  | false => 
    add_le_add_right h a


-- created on 2024-07-01
-- updated on 2025-03-15
