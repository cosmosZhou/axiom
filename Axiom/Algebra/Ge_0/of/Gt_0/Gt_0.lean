import Axiom.Algebra.Ge_0.of.Gt_0.Ge_0
import Axiom.Algebra.Ge.of.Gt
open Algebra


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α]
  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y > 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  apply Ge_0.of.Gt_0.Ge_0 h₀
  apply Ge.of.Gt h₁


-- created on 2025-03-23
