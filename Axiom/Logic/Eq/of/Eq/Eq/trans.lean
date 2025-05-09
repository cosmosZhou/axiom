import Axiom.Basic


@[main]
private lemma main
  {a b : α}
  {f : α → α → α}
-- given
  (h_a : f a b = a)
  (h_b : f a b = b) :
-- imply
  a = b :=
-- proof
  Eq.trans h_a.symm h_b


-- created on 2025-01-13
