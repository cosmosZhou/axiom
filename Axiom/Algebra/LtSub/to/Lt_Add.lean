import Axiom.Algebra.Lt.to.LtAddS

namespace Algebra.LtSub.to

theorem Lt_Add
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a - b < c) :
-- imply
  a < c + b := by
-- proof
  have h := Lt.to.LtAddS h b
  simp at h
  exact h


end Algebra.LtSub.to

-- created on 2024-11-27
