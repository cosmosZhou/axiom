import Axiom.Algebra.Mul.gt.Zero.is.AndGtS_0.ou.AndLtS_0
open Algebra


@[main]
private lemma main
  [Semiring α]
  [LinearOrder α]
  [ExistsAddOfLE α]
  [PosMulStrictMono α]
  [MulPosStrictMono α]
  [AddLeftStrictMono α]
  [AddLeftReflectLT α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  a > 0 ∧ b > 0 ∨ a < 0 ∧ b < 0 :=
  -- proof
  Mul.gt.Zero.is.AndGtS_0.ou.AndLtS_0.mp h


-- created on 2025-04-18
