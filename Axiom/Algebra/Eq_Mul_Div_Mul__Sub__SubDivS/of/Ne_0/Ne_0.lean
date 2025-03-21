import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.SubMulS.eq.Mul_Sub
import Axiom.Algebra.Eq_Div_Mul__Sub__SubInvS.of.Ne_0.Ne_0
open Algebra


@[main]
private lemma main
  [Field α]
  {x a b : α}
-- given
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
-- imply
  x / a - x / b = x * ((b - a) / (a * b)) := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [SubMulS.eq.Mul_Sub]
  rw [Eq_Div_Mul__Sub__SubInvS.of.Ne_0.Ne_0 h0 h1]


-- created on 2024-07-01
-- updated on 2025-03-01
