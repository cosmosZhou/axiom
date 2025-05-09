import Axiom.Basic


@[main]
private lemma nat
  {a b c : ℕ} :
-- imply
  a - (b + c) = a - b - c := by
-- proof
  rw [Nat.sub_add_eq]


@[main]
private lemma main
  [SubtractionCommMonoid α]
  {a b c : α} :
-- imply
  a - (b + c) = a - b - c := by
-- proof
  rw [sub_add_eq_sub_sub]


-- created on 2024-07-01
