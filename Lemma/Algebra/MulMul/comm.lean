import Lemma.Algebra.Mul.comm
import Lemma.Algebra.Mul_Mul.eq.MulMul
open Algebra


@[main]
private lemma main
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = a * c * b := by
-- proof
  rw [Mul.comm (b := c)]
  rw [Mul.comm (b := c)]
  rw [Mul_Mul.eq.MulMul]


-- created on 2024-11-29
