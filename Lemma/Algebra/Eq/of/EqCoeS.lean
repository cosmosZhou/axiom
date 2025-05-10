import Lemma.Algebra.EqCoeS.is.Eq
open Algebra


@[main]
private lemma nat
  [AddMonoidWithOne R]
  [CharZero R]
  {m n : ℕ}
-- given
  (h : (m : R) = (n : R)) :
-- imply
  m = n :=
-- proof
  EqCoeS.is.Eq.nat.mp h


@[main]
private lemma int
  [AddGroupWithOne R]
  [CharZero R]
  {m n : ℤ}
-- given
  (h : (m : R) = (n : R)) :
-- imply
  m = n :=
-- proof
  EqCoeS.is.Eq.int.mp h


@[main]
private lemma main
  [DivisionRing R]
  [CharZero R]
  {m n : ℚ}
-- given
  (h : (m : R) = (n : R)) :
-- imply
  m = n :=
-- proof
  EqCoeS.is.Eq.mp h


-- created on 2025-04-11
