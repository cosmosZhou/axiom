import Lemma.Algebra.Eq_Sub.of.EqAdd
import Lemma.Algebra.MulNeg.eq.NegMul
import Lemma.Algebra.MulNeg.eq.NegSquare
import Lemma.Algebra.Neg.lt.Zero.of.Gt_0
import Lemma.Algebra.Square.ge.Zero
import Lemma.Algebra.Lt.of.Lt.Le


@[main]
private lemma main
  [OrderedRing α]
  {a b : α}
-- given
  (h : a * b > 0)
  (left : Bool := true) :
-- imply
  match left with
  | true => a ≠ 0
  | false => b ≠ 0 := by
-- proof
  match left with
  | true =>
    by_contra h'
    rw [h'] at h
    simp at h
  | false =>
    by_contra h'
    rw [h'] at h
    simp at h


-- created on 2024-11-30
