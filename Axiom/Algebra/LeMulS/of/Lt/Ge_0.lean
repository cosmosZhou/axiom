import Axiom.Algebra.Le.of.Lt.relax
import Axiom.Algebra.LeMulS.of.Le.Ge_0
open Algebra


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a < b)
  (h2 : x ≥ 0) :
-- imply
  a * x ≤ b * x := by
-- proof
  have h := Le.of.Lt.relax h1
  apply LeMulS.of.Le.Ge_0 h h2


-- created on 2024-07-01
