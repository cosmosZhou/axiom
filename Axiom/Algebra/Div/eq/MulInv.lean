import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  [CommGroup α]
  {a b : α} :
-- imply
  a / b = b⁻¹ * a := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [Mul.comm]


-- created on 2024-11-29
