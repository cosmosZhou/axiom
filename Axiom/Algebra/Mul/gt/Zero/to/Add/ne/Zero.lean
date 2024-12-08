import Axiom.Algebra.EqAdd.to.Eq_Sub
import Axiom.Algebra.MulNeg.eq.NegMul
import Axiom.Algebra.MulNeg.eq.NegSquare
import Axiom.Algebra.Gt_0.to.Neg.lt.Zero
import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Lt.Le.to.Lt.trans

namespace Algebra.Mul.gt.Zero.to.Add.ne

theorem Zero
  [LinearOrderedRing α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  a + b ≠ 0 := by
-- proof
  by_contra h'
  have h' := EqAdd.to.Eq_Sub h'
  simp at h'
  rw [h'] at h
  rw [MulNeg.eq.NegSquare] at h
  have h := Gt_0.to.Neg.lt.Zero h
  simp at h
  have h := Lt.Le.to.Lt.trans h (Square.ge.Zero (a := b))
  simp at h


end Algebra.Mul.gt.Zero.to.Add.ne

-- created on 2024-11-29
