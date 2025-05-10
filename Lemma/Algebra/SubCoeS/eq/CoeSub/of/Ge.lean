import Lemma.Algebra.CoeSub.eq.SubCoeS.of.Ge
open Algebra


@[main]
private lemma main
  [AddGroupWithOne α]
  {a b : ℕ}
-- given
  (h : a ≥ b) :
-- imply
  a - b = ((a - b : ℕ) : α) :=
-- proof
  (CoeSub.eq.SubCoeS.of.Ge h).symm


-- created on 2025-05-04
