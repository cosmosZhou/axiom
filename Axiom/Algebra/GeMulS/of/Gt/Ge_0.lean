import Axiom.Algebra.Ge.of.Gt.relax
import Axiom.Algebra.GeMulS.of.Ge.Ge_0
open Algebra


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a > b)
  (h2 : x ≥ 0) :
-- imply
  a * x ≥ b * x := by
-- proof
  have h := Ge.of.Gt.relax h1
  apply GeMulS.of.Ge.Ge_0 h h2


-- created on 2024-07-01
