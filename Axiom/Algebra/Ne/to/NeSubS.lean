import Axiom.Algebra.Eq.to.EqAddS.right

namespace Algebra.Ne.to

theorem NeSubS
  [AddGroup α]
  {x y : α}
-- given
  (h : x ≠ y)
  (d : α) :
-- imply
  x - d ≠ y - d := by
-- proof
  intro h'
  have h' := Eq.to.EqAddS.right h' d
  simp at h'
  exact h h'


end Algebra.Ne.to

-- created on 2024-11-27
