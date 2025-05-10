import Lemma.Algebra.Add.eq.Mul_2
open Algebra


@[main]
private lemma main
  [NonAssocSemiring α]
  {a : α} :
-- imply
  a * 2 = a + a :=
-- proof
  Add.eq.Mul_2.symm


-- created on 2025-05-04
