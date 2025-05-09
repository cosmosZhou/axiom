import Axiom.Algebra.Add_Mul.eq.Mul_Add1
open Algebra


@[main]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  d * (1 + k) = d + d * k := 
-- proof
  Add_Mul.eq.Mul_Add1.symm


-- created on 2025-05-04
