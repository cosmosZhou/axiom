import Axiom.Basic


@[main]
private lemma main
  [AddCommMagma α]
  {a b : α} :
-- imply
  a + b = b + a := by
-- proof
  apply add_comm


-- created on 2024-07-01
