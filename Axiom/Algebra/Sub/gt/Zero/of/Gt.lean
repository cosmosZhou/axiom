import Axiom.Algebra.Sub.gt.Zero.of.Lt
open Algebra


@[main]
private lemma nat
  {x y : ℕ}
-- given
  (h : x > y) :
-- imply
  x - y > 0 :=
-- proof
  Sub.gt.Zero.of.Lt.nat h


@[main]
private lemma main
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x - y > 0 :=
-- proof
  Sub.gt.Zero.of.Lt h


-- created on 2025-03-15
-- updated on 2025-05-04
