import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.AddAdd.eq.Add_Add
import Axiom.Algebra.Add.comm
import Axiom.Algebra.Add_Add.eq.AddAdd
import Axiom.Algebra.Add_Neg.eq.Sub
open Algebra


@[main]
private lemma main
  [AddCommGroup α]
  {a b c : α} :
-- imply
  a - b + c = a + c - b := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [AddAdd.eq.Add_Add]
  rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]
  rw [Add_Neg.eq.Sub]


-- created on 2025-03-04
