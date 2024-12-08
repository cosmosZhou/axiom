import Axiom.Algebra.Lt.to.LtSubS
import Axiom.Algebra.Sub.eq.Zero
import Axiom.Algebra.Sub0.eq.Neg

namespace Algebra.Lt_0.to.Neg.gt

theorem Zero
  [OrderedAddCommGroup α]
  {a : α}
-- given
  (h : a < 0) :
-- imply
  -a > 0 := by
-- proof
  have h := Lt.to.LtSubS h a
  simp only [Sub.eq.Zero, Sub0.eq.Neg] at h
  exact h


end Algebra.Lt_0.to.Neg.gt

-- created on 2024-11-29
