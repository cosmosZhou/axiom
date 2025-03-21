import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul_Mul.eq.MulMul
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.Square.eq.Mul
import Axiom.Algebra.MulMul.eq.Mul_Mul
open Algebra


@[main]
private lemma main
  [Field α]
  {a b : α} :
-- imply
  (a * b)² = a² * b² := by
-- proof
  rw [Square.eq.Mul]
  rw [Mul_Mul.eq.MulMul]
  rw [Mul.comm (a := a * b)]
  rw [Mul_Mul.eq.MulMul]
  rw [Mul.eq.Square]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul.eq.Square]


-- created on 2024-07-01
-- updated on 2025-03-01
