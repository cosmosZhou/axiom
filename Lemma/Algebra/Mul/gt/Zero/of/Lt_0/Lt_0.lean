import Lemma.Algebra.Mul.gt.Zero.of.Gt_0.Gt_0
import Lemma.Algebra.Neg.gt.Zero.of.Lt_0
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {a b : α}
-- given
  (h₀ : a < 0)
  (h₁ : b < 0) :
-- imply
  a * b > 0 := by
-- proof
  have h₀ := Neg.gt.Zero.of.Lt_0 h₀
  have h₁ := Neg.gt.Zero.of.Lt_0 h₁
  have h := Mul.gt.Zero.of.Gt_0.Gt_0 h₀ h₁
  simp at h
  exact h


-- created on 2024-11-25
