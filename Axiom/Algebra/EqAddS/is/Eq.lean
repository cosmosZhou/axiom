import Axiom.Basic


@[main]
private lemma main
  [Add α]
  [IsLeftCancelAdd α]
  {a x y : α} :
-- imply
  a + x = a + y ↔ x = y :=
-- proof
  add_right_inj a


-- created on 2025-04-20
