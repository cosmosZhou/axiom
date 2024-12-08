import Axiom.Algebra.Le.to.LeAddS

namespace Algebra.LeSub.to

theorem Le_Add
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a - b ≤ c) :
-- imply
  a ≤ c + b := by
-- proof
  have h := Le.to.LeAddS h b
  simp at h
  exact h


end Algebra.LeSub.to

-- created on 2024-11-27
