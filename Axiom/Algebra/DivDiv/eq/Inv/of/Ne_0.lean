import Axiom.Algebra.Div_Mul.eq.Inv.of.Ne_0
import Axiom.Algebra.DivDiv.eq.Div_Mul
open Algebra


@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / b / a = b⁻¹ := by
-- proof
  rw [DivDiv.eq.Div_Mul]
  rw [Div_Mul.eq.Inv.of.Ne_0 h true]


-- created on 2025-03-03
