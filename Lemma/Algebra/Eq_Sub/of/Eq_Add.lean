import Lemma.Algebra.Add.comm
import Lemma.Algebra.EqSub.of.Eq_Add
open Algebra


@[main]
private lemma left
  [AddGroup α]
  {x y d : α}
-- given
  (h : y = x + d) :
-- imply
  x = y - d := by
-- proof
  have := EqSub.of.Eq_Add h
  apply Eq.symm this


@[main]
private lemma main
  [AddCommGroup α]
  {x y d : α}
-- given
  (h : y = d + x) :
-- imply
  x = y - d := by
-- proof
  rw [Add.comm] at h
  have := EqSub.of.Eq_Add h
  apply Eq.symm this


-- created on 2025-04-26
-- updated on 2025-05-05
