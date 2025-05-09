import Axiom.Algebra.Eq.ou.Lt.of.Le
import Axiom.Algebra.Le.of.Lt
import Axiom.Algebra.Mul.lt.Zero.of.Lt_0.Gt_0
open Algebra


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [MulPosStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y > 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  cases' Eq.ou.Lt.of.Le h₀ with hx hx
  ·
    simp_all
  ·
    apply Le.of.Lt
    apply Mul.lt.Zero.of.Lt_0.Gt_0 hx h₁


-- created on 2025-03-23
-- updated on 2025-05-05
