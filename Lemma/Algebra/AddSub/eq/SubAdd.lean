import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Algebra.Add.comm
import Lemma.Algebra.Add_Add.eq.AddAdd
import Lemma.Algebra.Add_Neg.eq.Sub
open Algebra


/--
In an additive commutative group, the expression \(a - b + c\) is equivalent to \(a + c - b\).
This lemma demonstrates that subtraction and addition can be reordered while preserving equality, leveraging the commutativity and associativity of the group operation.
The proof systematically applies fundamental group axioms to rearrange terms and verify the equivalence.
-/
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
-- updated on 2025-04-04
