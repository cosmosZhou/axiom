import Axiom.Algebra.Eq_Sub.of.EqAdd
import Axiom.Algebra.MulNeg.eq.NegMul
import Axiom.Algebra.MulNeg.eq.NegSquare
import Axiom.Algebra.Neg.lt.Zero.of.Gt_0
import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Lt.of.Lt.Le


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
