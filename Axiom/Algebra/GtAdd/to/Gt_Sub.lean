import Axiom.Algebra.Gt.to.GtSubS


namespace Algebra.GtAdd.to

theorem Gt_Sub
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b > c) :
-- imply
  a > c - b := by
-- proof
  have h := Gt.to.GtSubS h b
  simp at h
  exact h



end Algebra.GtAdd.to

-- created on 2024-11-26
