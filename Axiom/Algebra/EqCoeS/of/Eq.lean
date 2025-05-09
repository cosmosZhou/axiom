import Axiom.Algebra.EqCoeS.is.Eq
open Algebra


@[main]
private lemma nat
  [AddMonoidWithOne R]
  [CharZero R]
  {a b : ℕ}
-- given
  (h : a = b) :
-- imply
  (a : R) = (b : R) :=
-- proof
  EqCoeS.is.Eq.nat.mpr h


@[main]
private lemma int
  [AddGroupWithOne R]
  [CharZero R]
  {a b : ℤ}
-- given
  (h : a = b) :
-- imply
  (a : R) = (b : R) :=
-- proof
  EqCoeS.is.Eq.int.mpr h


@[main]
private lemma main
  [DivisionRing R]
  [CharZero R]
  {a b : ℚ}
-- given
  (h : a = b) :
-- imply
  (a : R) = (b : R) :=
-- proof
  EqCoeS.is.Eq.mpr h


-- created on 2025-04-11
-- updated on 2025-04-20
