import Axiom.Algebra.Ge.of.Gt
import Axiom.Algebra.Gt_0.of.Gt_0.Gt_0
import Axiom.Algebra.Eq.ou.Gt.of.Ge
open Algebra


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y > 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  cases' Eq.ou.Gt.of.Ge h₀ with hx hx
  simp_all
  have := Gt_0.of.Gt_0.Gt_0 hx h₁
  exact Ge.of.Gt this


-- created on 2025-03-23
