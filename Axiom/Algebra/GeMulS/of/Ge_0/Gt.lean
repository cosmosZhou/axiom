import Axiom.Algebra.Ge.of.Gt.relax
import Axiom.Algebra.GeMulS.of.Ge_0.Ge
open Algebra


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a > b) :
-- imply
  x * a ≥ x * b := by
-- proof
  have h := Ge.of.Gt.relax h2
  apply GeMulS.of.Ge_0.Ge h1 h


-- created on 2024-07-01
