import Axiom.Algebra.MulMul.eq.Mul_Mul
open Algebra


@[main]
private lemma main
  [Semigroup α]
  {a b : α} :
-- imply
  a * (b * c) = a * b * c := by
-- proof
  rw [MulMul.eq.Mul_Mul]


-- created on 2024-07-01
