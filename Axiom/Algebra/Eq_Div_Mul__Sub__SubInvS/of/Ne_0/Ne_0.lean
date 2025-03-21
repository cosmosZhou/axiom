import Axiom.Algebra.Div1.eq.Inv
import Axiom.Algebra.SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0
open Algebra


@[main]
private lemma main
  [Field α]
  {a b : α}
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
-- imply
  a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
-- proof
  rw [
    ← Div1.eq.Inv,
    ← Div1.eq.Inv,
    SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0 h0 h1
  ]
  simp


-- created on 2024-07-01
