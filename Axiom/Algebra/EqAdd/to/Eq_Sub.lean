import Axiom.Algebra.Eq.to.EqSubS
import Axiom.Algebra.SubAdd.cancel

namespace Algebra.EqAdd.to

theorem Eq_Sub
  [AddGroup α]
  {x y d : α}
-- given
  (h : d + x = y) :
-- imply
  d = y - x := by
-- proof
  have h := Eq.to.EqSubS h x
  simp [SubAdd.cancel] at h
  exact h


end Algebra.EqAdd.to

-- created on 2024-07-01
