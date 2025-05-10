import Lemma.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  a ⊓ b = b ⊓ a :=
-- proof
  min_comm a b


-- created on 2025-05-07
