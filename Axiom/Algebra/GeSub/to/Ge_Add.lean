import Axiom.Algebra.Ge.to.GeAddS

namespace Algebra.GeSub.to

theorem Ge_Add
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a - b ≥ c) :
-- imply
  a ≥ c + b := by
-- proof
  have h := Ge.to.GeAddS h b
  simp at h
  exact h


end Algebra.GeSub.to

-- created on 2024-11-27
