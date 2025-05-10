import Lemma.Algebra.Sub.eq.AddNeg
import Lemma.Algebra.Ite.eq.AddIte
import Lemma.Algebra.EqAddS.of.Eq
import Lemma.Algebra.Ite.eq.NegIte
open Algebra


@[main]
private lemma main
  [Decidable p]
  [AddCommGroup α]
  {a b c : α} :
-- imply
  (if p then
    c - a
  else
    c - b) = c - if p then
    a
  else
    b := by
-- proof
  rw [Sub.eq.AddNeg]
  rw [Sub.eq.AddNeg]
  rw [Ite.eq.AddIte]
  rw [Sub.eq.AddNeg]
  apply EqAddS.of.Eq
  apply Ite.eq.NegIte


-- created on 2025-04-26
