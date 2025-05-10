import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.Add.comm
open Algebra


@[main]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  -a + b = b - a := by
-- proof
  rw [Add.comm]
  rw [Sub.eq.Add_Neg]


-- created on 2025-03-27
