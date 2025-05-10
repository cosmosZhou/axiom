import Lemma.Algebra.NegSub.eq.Sub
open Algebra


@[main]
private lemma main
  [AddGroup α]
  -- [Neg α]
  {a b : α} :
-- imply
  a - b = -(b - a) := by
-- proof
  rw [NegSub.eq.Sub]


-- created on 2024-11-29
