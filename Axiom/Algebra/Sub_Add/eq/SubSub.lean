import Axiom.Basic


@[main]
private lemma main
  [SubtractionCommMonoid α]
  {a b c : α} :
-- imply
  a - (b + c) = a - b - c := by
-- proof
  rw [sub_add_eq_sub_sub]


-- created on 2024-07-01
