import Axiom.Algebra.LeMulS.of.Ge_0.Le
open Algebra


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a ≥ b) :
-- imply
  x * a ≥ x * b :=
-- proof
  LeMulS.of.Ge_0.Le h1 h2


-- created on 2024-07-01
