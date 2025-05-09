import Axiom.Algebra.AddMul.eq.MulAdd_1
open Algebra


@[main]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  (k + 1) * d = k * d + d := 
-- proof
  AddMul.eq.MulAdd_1.symm


-- created on 2025-05-04
