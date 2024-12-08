import Axiom.Algebra.Lt.to.Le_Sub_1
import Axiom.Algebra.Le.to.LeAddS

namespace Algebra.Lt.to

theorem LeAdd_1
  {x y : ℤ}
-- given
  (h : x < y) :
-- imply
  x + 1 ≤ y := by
-- proof
  have h' := Lt.to.Le_Sub_1 h

  have h' := Le.to.LeAddS h' 1

  simp at h'

  exact h'

end Algebra.Lt.to

-- created on 2024-07-01
