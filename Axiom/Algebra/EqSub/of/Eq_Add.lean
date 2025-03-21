import Axiom.Algebra.Eq_Sub.of.EqAdd
open Algebra


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
