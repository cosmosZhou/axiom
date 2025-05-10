import Lemma.Basic


@[main]
private lemma nat
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ}
-- given
  (h : a < b) :
-- imply
  (a : R) < (b : R) := by
-- proof
  apply Nat.cast_lt.mpr h


@[main]
private lemma int
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
  {a b : ℤ}
-- given
  (h : a < b) :
-- imply
  (a : R) < (b : R) := by
-- proof
  apply Int.cast_lt.mpr h


@[main]
private lemma main
  [LinearOrderedField R]
  {a b : ℚ}
-- given
  (h : a < b) :
-- imply
  (a : R) < (b : R) := by
-- proof
  apply Rat.cast_lt.mpr h


-- created on 2025-03-29
-- updated on 2025-04-26
