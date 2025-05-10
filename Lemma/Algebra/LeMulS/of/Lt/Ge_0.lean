import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.LeMulS.of.Le.Ge_0
open Algebra


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h₀ : a < b)
  (h₁ : x ≥ 0) :
-- imply
  a * x ≤ b * x := by
-- proof
  have h := Le.of.Lt h₀
  apply LeMulS.of.Le.Ge_0 h h₁


-- created on 2024-07-01
