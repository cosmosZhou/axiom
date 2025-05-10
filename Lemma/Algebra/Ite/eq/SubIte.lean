import Lemma.Algebra.Sub.eq.AddNeg
import Lemma.Algebra.Ite.eq.Add_Ite
open Algebra


@[main]
private lemma main
  [Decidable p]
  [AddCommGroup α]
  {a b c : α} :
-- imply
  (if p then
    a - c
  else
    b - c) = (if p then
    a
  else
    b) - c := by
-- proof
  rw [Sub.eq.AddNeg]
  rw [Sub.eq.AddNeg]
  rw [Sub.eq.AddNeg]
  apply Ite.eq.Add_Ite


-- created on 2025-04-26
