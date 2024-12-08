import Axiom.Algebra.EqAdd.to.Eq_Sub
import Axiom.Algebra.MulNeg.eq.NegMul
import Axiom.Algebra.MulNeg.eq.NegSquare
import Axiom.Algebra.Gt_0.to.Neg.lt.Zero
import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Lt.Le.to.Lt.trans

namespace Algebra.Mul.gt.Zero.to

theorem Ne_0
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
  cases left

  case true =>
    by_contra h'
    rw [h'] at h
    simp at h

  case false =>
    by_contra h'
    rw [h'] at h
    simp at h

end Algebra.Mul.gt.Zero.to

-- created on 2024-11-30
