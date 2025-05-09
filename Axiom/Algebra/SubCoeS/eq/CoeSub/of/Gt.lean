import Axiom.Algebra.SubCoeS.eq.CoeSub.of.Ge
import Axiom.Algebra.Ge.of.Gt
open Algebra


@[main]
private lemma main
  [AddGroupWithOne α]
  {a b : ℕ}
-- given
  (h : a > b) :
-- imply
  a - b = ((a - b : ℕ) : α) := by
-- proof
  have h := Ge.of.Gt h
  apply SubCoeS.eq.CoeSub.of.Ge h


-- created on 2025-05-04
