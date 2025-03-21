import Axiom.Algebra.LtMulS.of.Lt.Gt_0
open Algebra


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α]
  {x a b : α}
-- given
  (h1 : a > b)
  (h2 : x > 0) :
-- imply
  a * x > b * x := by
-- proof
  apply LtMulS.of.Lt.Gt_0 h1 h2


-- created on 2024-07-01
