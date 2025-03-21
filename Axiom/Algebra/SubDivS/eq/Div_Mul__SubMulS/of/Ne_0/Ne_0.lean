import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.SubDivS.eq.DivSub
import Axiom.Algebra.DivMul.eq.Mul_Div
import Axiom.Algebra.Div_Mul.eq.Inv.of.Ne_0
open Algebra


@[main]
private lemma main
  [Field α]
  {a b x y : α}
-- given
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
-- imply
  x / a - y / b = (x * b - y * a) / (a * b) := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [← SubDivS.eq.DivSub]
  rw [DivMul.eq.Mul_Div]
  rw [Div_Mul.eq.Inv.of.Ne_0 h1 true]
  rw [DivMul.eq.Mul_Div]
  rw [Div_Mul.eq.Inv.of.Ne_0 h0]


-- created on 2024-07-01
-- updated on 2025-03-01
