import Axiom.Basic


@[main]
private lemma nat
  [AddMonoidWithOne R]
  [CharZero R]
  {a b : ℕ} :
-- imply
  (a : R) = (b : R) ↔ a = b :=
-- proof
  Nat.cast_inj


@[main]
private lemma int
  [AddGroupWithOne R]
  [CharZero R]
  {a b : ℤ} :
-- imply
  (a : R) = (b : R) ↔ a = b :=
-- proof
  Int.cast_inj


@[main]
private lemma main
  [DivisionRing R]
  [CharZero R]
  {a b : ℚ} :
-- imply
  (a : R) = (b : R) ↔ a = b :=
-- proof
  Rat.cast_inj


-- created on 2025-04-11
-- updated on 2025-04-20
