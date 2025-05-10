import Lemma.Algebra.Eq_Sub.of.EqAdd
import Lemma.Algebra.MulNeg.eq.NegMul
import Lemma.Algebra.MulNeg.eq.NegSquare
import Lemma.Algebra.Neg.lt.Zero.of.Gt_0
import Lemma.Algebra.Square.ge.Zero
import Lemma.Algebra.Lt.of.Lt.Le
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  a + b ≠ 0 := by
-- proof
  by_contra h'
  have h' := Eq_Sub.of.EqAdd h'
  simp at h'
  rw [h'] at h
  rw [MulNeg.eq.NegSquare] at h
  have h := Neg.lt.Zero.of.Gt_0 h
  simp at h
  have h := Lt.of.Lt.Le h (Square.ge.Zero (a := b))
  simp at h


-- created on 2024-11-29
