import Axiom.Algebra.AddSub.eq.SubAdd
open Algebra


@[main]
private lemma main
  [AddCommGroup α]
  {a b c : α} :
-- imply
  a + b - c = a - c + b := by
-- proof
  rw [AddSub.eq.SubAdd]


-- created on 2025-03-31
