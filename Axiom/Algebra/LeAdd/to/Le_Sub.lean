import Axiom.Algebra.Le.to.LeSubS

namespace Algebra.LeAdd.to

theorem Le_Sub
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b ≤ c) :
-- imply
  a ≤ c - b := by
-- proof
  have h := Le.to.LeSubS h b
  simp at h
  exact h


end Algebra.LeAdd.to

-- created on 2024-11-27
