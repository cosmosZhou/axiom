import Lemma.Algebra.Sub.gt.Zero.is.Lt
open Algebra


@[main]
private lemma nat
  {a b : ℕ}
-- given
  (h : a < b) :
-- imply
  b - a > 0 :=
-- proof
  Sub.gt.Zero.is.Lt.nat.mpr h


/--
This lemma establishes that in an ordered additive group with right-strictly monotonic addition, if `a` is less than `b`, then the difference `b - a` is positive.
It leverages the equivalence between the inequality `a < b` and the positivity of `b - a`, as defined by the underlying order and algebraic structure.
-/
@[main]
private lemma main
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  b - a > 0 :=
-- proof
  Sub.gt.Zero.is.Lt.mpr h


-- created on 2024-11-25
-- updated on 2025-05-04
