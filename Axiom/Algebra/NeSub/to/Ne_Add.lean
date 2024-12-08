import Axiom.Algebra.Ne.to.NeAddS

namespace Algebra.NeSub.to

theorem Ne_Add
  [AddGroup α]
  {x a b: α}
-- given
  (h : x - b ≠ a) :
-- imply
  x ≠ a + b := by
-- proof
  have h := Ne.to.NeAddS h b
  simp at h
  exact h


end Algebra.NeSub.to

-- created on 2024-11-27
