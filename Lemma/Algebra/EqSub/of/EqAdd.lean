import Lemma.Algebra.Eq_Sub.of.EqAdd
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x y d : α}
-- given
  (h : d + x = y) :
-- imply
  y - x = d := by
-- proof
  have := Eq_Sub.of.EqAdd h
  apply Eq.symm this


-- created on 2025-04-16
