import Axiom.Basic


@[main]
private lemma main
  [Add α]
  {x y : α}
-- given
  (h : x = y)
  (d : α)
  (left : Bool := false):
-- imply
  match left with
  | true =>
    d + x = d + y
  | false =>
    x + d = y + d := by
-- proof
  match left with
  | true =>
    rw [h]
  | false =>
    rw [h]


-- created on 2024-12-31
