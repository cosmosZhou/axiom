import Axiom.Basic


@[main]
private lemma main
  [CommMagma α]
  {a b : α} :
-- imply
  a * b = b * a := by
-- proof
  apply mul_comm


-- created on 2024-07-01
