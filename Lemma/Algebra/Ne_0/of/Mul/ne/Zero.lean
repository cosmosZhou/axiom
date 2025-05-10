import Lemma.Algebra.Mul0.eq.Zero
import Lemma.Algebra.Mul_0.eq.Zero
open Algebra


@[main]
private lemma left
  [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b ≠ 0) :
-- imply
  a ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h
  rw [Mul0.eq.Zero] at h
  simp at h


@[main]
private lemma main
  [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b ≠ 0) :
-- imply
  b ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h
  rw [Mul_0.eq.Zero] at h
  simp at h


-- created on 2025-04-12
