import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.AddMulS.eq.MulAdd
open Algebra


@[main]
private lemma main
  [Field α]
  {x y a : α} :
-- imply
  x / a + y / a = (x + y) / a := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [AddMulS.eq.MulAdd]


-- created on 2024-07-01
