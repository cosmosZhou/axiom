import Axiom.Algebra.AddMulS.eq.MulAdd
import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.NegMul.eq.MulNeg
open Algebra


@[main]
private lemma main
  [Ring α]
  {x a b : α} :
-- imply
  a * x - b * x = (a - b) * x := by
-- proof
  rw [
    Sub.eq.Add_Neg (a := a),
    AddMulS.eq.MulAdd.symm,
    Sub.eq.Add_Neg,
    NegMul.eq.MulNeg
  ]


-- created on 2024-07-01
