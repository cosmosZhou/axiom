import Axiom.Algebra.Lt.to.LtSubS

namespace Algebra.LtAdd.to

theorem Lt_Sub
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b < c) :
-- imply
  a < c - b := by
-- proof
  have h := Lt.to.LtSubS h b
  simp at h
  exact h


end Algebra.LtAdd.to

-- created on 2024-11-27
