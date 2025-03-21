import Axiom.Algebra.GtSub__0.equ.Lt
open Algebra


@[main]
private lemma main
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  b - a > 0 :=
-- proof
  GtSub__0.equ.Lt.mpr h


-- created on 2024-11-25
