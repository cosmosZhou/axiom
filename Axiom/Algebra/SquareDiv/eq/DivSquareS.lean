import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul_Div.eq.DivMul
import Axiom.Algebra.MulDiv.eq.DivMul
import Axiom.Algebra.DivDiv.eq.Div_Mul
open Algebra


@[main]
private lemma main
  [Field α]
  {a b : α} :
-- imply
  (a / b)² = a² / b² := by
-- proof
  rw [Square.eq.Mul]
  rw [Mul_Div.eq.DivMul]
  rw [MulDiv.eq.DivMul]
  rw [Mul.eq.Square]
  rw [DivDiv.eq.Div_Mul]
  rw [Mul.eq.Square]


-- created on 2024-07-01
