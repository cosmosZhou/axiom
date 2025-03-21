import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.SubMulS.eq.MulSub
open Algebra


@[main]
private lemma main
  [Field α]
  {x y a : α} :
-- imply
  x / a - y / a = (x - y) / a := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [SubMulS.eq.MulSub]


-- created on 2024-07-01
-- updated on 2025-03-01
