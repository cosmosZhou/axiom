import Axiom.Algebra.Ne.to.NeSubS

namespace Algebra.NeAdd.to

theorem Ne_Sub
  [AddGroup α]
  {x a b: α}
-- given
  (h : x + b ≠ a) :
-- imply
  x ≠ a - b := by
-- proof
  have h := Ne.to.NeSubS h b
  simp at h
  exact h


end Algebra.NeAdd.to

-- created on 2024-11-27
