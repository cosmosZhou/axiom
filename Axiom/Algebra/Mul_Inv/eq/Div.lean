import Axiom.Algebra.Div.eq.Mul_Inv
open Algebra


@[simp, main]
private lemma main
  [DivInvMonoid α]
  {a b : α} :
-- imply
  a * b⁻¹ = a / b := by
-- proof
  rw [Div.eq.Mul_Inv]


-- created on 2024-07-01
