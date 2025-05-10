import Lemma.Basic


@[main]
private lemma main
  [SubNegMonoid α]
  {a b c : α} :
-- imply
  a + (b - c) = a + b - c := by
-- proof
  rw [add_sub_assoc]


-- created on 2024-07-01
