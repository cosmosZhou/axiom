import Axiom.Algebra.Add.comm
import Axiom.Algebra.Ite.eq.Add_Ite
open Algebra


@[main]
private lemma main
  [Decidable p]
  [AddCommGroup α]
  {a b c : α} :
-- imply
  (if p then
    a + c
  else
    b + c) = (if p then
    a
  else
    b) + c := by
-- proof
  rw [Add.comm]
  rw [Add.comm (a := b)]
  rw [Add.comm (b := c)]
  apply Ite.eq.Add_Ite


-- created on 2025-04-26
