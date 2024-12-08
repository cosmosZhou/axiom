import Axiom.Algebra.Le.to.LeSubS
import Axiom.Algebra.Sub.eq.Zero
import Axiom.Algebra.Sub0.eq.Neg

namespace Algebra.Le_0.to.Neg.ge

theorem Zero
  [OrderedAddCommGroup α]
  {a : α}
-- given
  (h : a ≤ 0) :
-- imply
  -a ≥ 0 := by
-- proof
  have h := Le.to.LeSubS h a
  simp only [Sub.eq.Zero, Sub0.eq.Neg] at h
  exact h


end Algebra.Le_0.to.Neg.ge

-- created on 2024-11-29
