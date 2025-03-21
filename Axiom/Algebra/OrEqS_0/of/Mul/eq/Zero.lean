import Axiom.Algebra.EqMul__0.equ.OrEqS_0
open Algebra


@[main]
private lemma main
  [MulZeroClass α] [NoZeroDivisors α]
  {a b : α}
-- given
  (h : a * b = 0) :
-- imply
  a = 0 ∨ b = 0 := by
-- proof
  exact EqMul__0.equ.OrEqS_0.mp h


-- created on 2024-11-29
