import Axiom.Algebra.Mul.eq.Zero.is.OrEqS_0
open Algebra


@[main]
private lemma main
  [MulZeroClass α] [NoZeroDivisors α]
  {a b : α}
-- given
  (h : a = 0 ∨ b = 0) :
-- imply
  a * b = 0 :=
-- proof
  Mul.eq.Zero.is.OrEqS_0.mpr h
