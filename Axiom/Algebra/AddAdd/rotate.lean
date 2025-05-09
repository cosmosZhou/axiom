import Axiom.Algebra.AddAdd.eq.Add_Add
import Axiom.Algebra.Add.comm
open Algebra


@[main]
private lemma main
  [AddCommSemigroup α]
  {a b : α} :
-- imply
  a + b + c = b + c + a := by
-- proof
  rw [AddAdd.eq.Add_Add]
  rw [Add.comm]


-- created on 2025-03-29
