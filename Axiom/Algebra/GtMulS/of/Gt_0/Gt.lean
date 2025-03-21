import Axiom.Algebra.LtMulS.of.Gt_0.Lt
open Algebra


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h1 : x > 0)
  (h2 : a > b) :
-- imply
  x * a > x * b :=
-- proof
  LtMulS.of.Gt_0.Lt h1 h2


-- created on 2024-07-01
