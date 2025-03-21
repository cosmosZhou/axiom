import Axiom.Algebra.EqMul1
import Axiom.Algebra.Div.eq.Mul_Inv
open Algebra


@[main]
private lemma main
  [DivInvMonoid α]
  {x : α} :
-- imply
  x⁻¹ = 1 / x := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [EqMul1]


-- created on 2024-11-25
-- updated on 2025-03-02
