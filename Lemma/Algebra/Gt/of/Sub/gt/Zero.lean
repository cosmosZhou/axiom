import Lemma.Algebra.Sub.gt.Zero.is.Lt
open Algebra


@[main]
private lemma nat
  {x y : ℕ}
-- given
  (h : x - y > 0) :
-- imply
  x > y :=
-- proof
  Sub.gt.Zero.is.Lt.nat.mp h


@[main]
private lemma main
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {x y : α}
-- given
  (h : x - y > 0) :
-- imply
  x > y :=
-- proof
  Sub.gt.Zero.is.Lt.mp h


-- created on 2025-03-30
