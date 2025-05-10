import Lemma.Algebra.Add.eq.Mul2
open Algebra


@[main]
private lemma main
  [NonAssocSemiring α]
  {a : α} :
-- imply
  2 * a = a + a :=
-- proof
  Add.eq.Mul2.symm


-- created on 2025-05-04
