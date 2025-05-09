import Axiom.Algebra.Eq.ou.Gt.of.Ge
import Axiom.Algebra.Mul.le.Zero.of.Le_0.Gt_0
open Algebra


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [MulPosStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y ≥ 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  cases' Eq.ou.Gt.of.Ge h₁ with hy hy
  ·
    simp_all
  ·
    apply Mul.le.Zero.of.Le_0.Gt_0 h₀ hy


-- created on 2025-03-24
-- updated on 2025-05-05
