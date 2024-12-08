import Axiom.Algebra.Gt.to.GtSubS
import Axiom.Algebra.Sub.eq.Zero
import Axiom.Algebra.Sub0.eq.Neg

namespace Algebra.Gt_0.to.Neg.lt

theorem Zero
  [OrderedAddCommGroup α]
  {a : α}
-- given
  (h : a > 0) :
-- imply
  -a < 0 := by
-- proof
  have h := Gt.to.GtSubS h a
  simp only [Sub.eq.Zero, Sub0.eq.Neg] at h
  exact h


end Algebra.Gt_0.to.Neg.lt

-- created on 2024-11-29
