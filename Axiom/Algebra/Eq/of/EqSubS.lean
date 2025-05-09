import Axiom.Algebra.EqAddS.of.Eq
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x y : α}
-- given
  (h : x - d = y - d)
  (d : α) :
-- imply
  x = y := by
-- proof
  have h := EqAddS.of.Eq h d
  simp_all [h]


-- created on 2025-03-30
