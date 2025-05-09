import Axiom.Algebra.Mul.lt.Zero.is.OrAndSLt_0Gt_0
open Algebra


@[main]
private lemma main
  [Ring α]
  [LinearOrder α]
  [PosMulStrictMono α]
  [MulPosStrictMono α]
  [AddLeftReflectLT α]
  [AddLeftStrictMono α]
  {a b : α}
-- given
  (h : a * b < 0) :
-- imply
  a < 0 ∧ b > 0 ∨ b < 0 ∧ a > 0 := 
-- proof
  Mul.lt.Zero.is.OrAndSLt_0Gt_0.mp h


-- created on 2025-03-30
