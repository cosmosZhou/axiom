import Axiom.Algebra.Mul_Add.eq.AddMulS
import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.NegMul.eq.Mul_Neg
open Algebra


@[main]
private lemma main
  [Ring α]
  {x a b : α} :
-- imply
  x * a - x * b = x * (a - b) := by
-- proof
  rw [
    Sub.eq.Add_Neg (a := a),
    Mul_Add.eq.AddMulS,
    Sub.eq.Add_Neg,
    NegMul.eq.Mul_Neg
  ]


-- created on 2024-07-01
