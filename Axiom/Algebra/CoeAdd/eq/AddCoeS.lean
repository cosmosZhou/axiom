import Axiom.Basic


@[main]
private lemma nat
  [AddMonoidWithOne α]
  {a b : ℕ} :
-- imply
  ((a + b : ℕ) : α) = a + b :=
-- proof
  Nat.cast_add a b


@[main]
private lemma int
  [AddGroupWithOne α]
  {a b : ℤ} :
-- imply
  ((a + b : ℤ) : α) = a + b :=
-- proof
  Int.cast_add a b


@[main]
private lemma main
  [DivisionRing α]
  [CharZero α]
  {a b : ℚ} :
-- imply
  ↑(a + b) = (a + b : α) :=
-- proof
  Rat.cast_add a b


-- created on 2025-03-25
