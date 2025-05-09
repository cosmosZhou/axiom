import Axiom.Algebra.CoeSub.eq.SubCoeS
open Algebra


@[main]
private lemma int
  [AddGroupWithOne α]
  {a b : ℤ} :
-- imply
  a - b = ((a - b : ℤ) : α) := by
-- proof
  rw [← CoeSub.eq.SubCoeS.int]


@[main]
private lemma main
  [DivisionRing α]
  [CharZero α]
  {a b : ℚ} :
-- imply
  (a - b : α) = ↑(a - b) := by
-- proof
  rw [← CoeSub.eq.SubCoeS]


-- created on 2025-04-04
-- updated on 2025-05-04
