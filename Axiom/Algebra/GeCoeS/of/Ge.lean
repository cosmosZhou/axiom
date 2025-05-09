import Axiom.Algebra.LeCoeS.of.Le
open Algebra


@[main]
private lemma nat
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ}
-- given
  (h : a ≥ b) :
-- imply
  (a : R) ≥ (b : R) :=
-- proof
  LeCoeS.of.Le.nat h


@[main]
private lemma int
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
  {a b : ℤ}
-- given
  (h : a ≥ b) :
-- imply
  (a : R) ≥ (b : R) :=
-- proof
  LeCoeS.of.Le.int h


@[main]
private lemma main
  [LinearOrderedField R]
  {a b : ℚ}
-- given
  (h : a ≥ b) :
-- imply
  (a : R) ≥ (b : R) :=
-- proof
  LeCoeS.of.Le h


-- created on 2025-03-29
