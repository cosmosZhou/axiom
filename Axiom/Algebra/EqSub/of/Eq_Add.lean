import Axiom.Algebra.Eq_Sub.of.EqAdd
import Axiom.Algebra.EqSubAdd
open Algebra


@[main]
private lemma left
  [AddCommGroup α]
  {x y d : α}
-- given
  (h : y = d + x) :
-- imply
  y - d = x := by
-- proof
  rw [h]
  rw [EqSubAdd.left]


@[main]
private lemma main
  [AddGroup α]
  {x y d : α}
-- given
  (h : y = d + x) :
-- imply
  y - x = d :=
-- proof
  (Eq_Sub.of.EqAdd h.symm).symm


-- created on 2024-11-27
-- updated on 2025-04-26
