import Axiom.Algebra.AbsMul.eq.MulAbsS
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α} :
-- imply
  |x| * |y| = |x * y| := by
-- proof
  have := AbsMul.eq.MulAbsS x y
  apply Eq.symm this


-- created on 2025-04-18
-- updated on 2025-04-19
