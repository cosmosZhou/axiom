import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.Mul.ge.Zero.is.AndGeS_0.ou.AndLeS_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x y : α}
-- given
  (h : x * y ≥ 0) :
-- imply
  x / y ≥ 0 := by
-- proof
  -- Use the property that the product of two elements is non-negative if and only if both are non-negative or both are non-positive.
  rw [Div.eq.Mul_Inv]
  -- Split the proof into two cases based on the signs of x and y.
  cases' le_total 0 x with hx hx <;>
  ·
    cases' le_total 0 y with hy hy <;>
    ·
      cases' le_total 0 y⁻¹ with hy_inv hy_inv <;>
      ·
        simp_all [Mul.ge.Zero.is.AndGeS_0.ou.AndLeS_0]


-- created on 2025-03-23
