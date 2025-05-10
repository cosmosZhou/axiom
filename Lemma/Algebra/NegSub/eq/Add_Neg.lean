import Lemma.Algebra.NegSub.eq.Sub
import Lemma.Algebra.Add_Neg.eq.Sub
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  -(b - a) = a + (-b) := by
-- proof
  rw [NegSub.eq.Sub]
  rw [Add_Neg.eq.Sub]


-- created on 2025-03-29
