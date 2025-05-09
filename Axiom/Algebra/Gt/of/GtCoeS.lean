import Axiom.Algebra.Lt.of.LtCoeS
open Algebra


@[main]
private lemma nat
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ}
-- given
  (h : (a : R) > (b : R)) :
-- imply
  a > b :=
-- proof
  Lt.of.LtCoeS.nat h


@[main]
private lemma int
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
  {a b : ℤ}
-- given
  (h : (a : R) > (b : R)) :
-- imply
  a > b :=
-- proof
  Lt.of.LtCoeS.int h


@[main]
private lemma main
  [LinearOrderedField R]
  {a b : ℚ}
-- given
  (h : (a : R) > (b : R)) :
-- imply
  a > b :=
-- proof
  Lt.of.LtCoeS h


-- created on 2025-05-04
