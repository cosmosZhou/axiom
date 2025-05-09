import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.Add.comm
import Axiom.Algebra.Add_Neg.eq.Sub
open Algebra


@[main]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  -a - b = -b - a := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [Add.comm]
  rw [Add_Neg.eq.Sub]


-- created on 2025-03-27
