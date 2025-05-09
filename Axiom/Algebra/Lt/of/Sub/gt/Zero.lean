import Axiom.Algebra.Sub.gt.Zero.is.Lt
open Algebra


private lemma nat
  {x y : ℕ}
-- given
  (h : y - x > 0) :
-- imply
  x < y :=
-- proof
  Sub.gt.Zero.is.Lt.nat.mp h


@[main]
private lemma main
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {x y : α}
-- given
  (h : y - x > 0) :
-- imply
  x < y :=
-- proof
  Sub.gt.Zero.is.Lt.mp h


-- created on 2025-04-06
-- updated on 2025-05-04
