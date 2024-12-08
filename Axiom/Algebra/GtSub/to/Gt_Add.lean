import Axiom.Algebra.Gt.to.GtAddS


namespace Algebra.GtSub.to

theorem Gt_Add
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a - b > c) :
-- imply
  a > c + b := by
-- proof
  have h := Gt.to.GtAddS h b
  simp at h
  exact h


end Algebra.GtSub.to

-- created on 2024-11-26
