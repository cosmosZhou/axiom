import Axiom.Algebra.Ge.to.GeSubS

namespace Algebra.GeAdd.to

theorem Ge_Sub
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b ≥ c) :
-- imply
  a ≥ c - b := by
-- proof
  have h := Ge.to.GeSubS h b
  simp at h
  simp
  exact h


end Algebra.GeAdd.to

-- created on 2024-11-27
