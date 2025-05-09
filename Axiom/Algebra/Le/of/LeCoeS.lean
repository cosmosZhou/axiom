import Axiom.Basic


@[main]
private lemma nat
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ}
-- given
  (h : (a : R) ≤ (b : R)) :
-- imply
  a ≤ b :=
-- proof
  Nat.cast_le.mp h


@[main]
private lemma int
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
  {a b : ℤ}
-- given
  (h : (a : R) ≤ (b : R)) :
-- imply
  a ≤ b :=
-- proof
  Int.cast_le.mp h


@[main]
private lemma main
  [LinearOrderedField R]
  {a b : ℚ}
-- given
  (h : (a : R) ≤ (b : R)) :
-- imply
  a ≤ b :=
-- proof
  Rat.cast_le.mp h


-- created on 2025-03-30
