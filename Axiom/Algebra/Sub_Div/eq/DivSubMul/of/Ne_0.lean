import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.MulSub.eq.SubMulS
open Algebra


@[main]
private lemma main
  [Field α]
  {a b x : α}
-- given
  (h : b ≠ 0) :
-- imply
  x - a / b = (x * b - a) / b := by
-- proof
  rw [
    Div.eq.Mul_Inv,
    Div.eq.Mul_Inv
  ]
  
  rw [MulSub.eq.SubMulS]
  simp [h]


-- created on 2025-01-14
