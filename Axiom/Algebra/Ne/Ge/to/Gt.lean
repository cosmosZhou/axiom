import Axiom.Algebra.Ge.Le.to.Eq
namespace Algebra.Ne.Ge.to

theorem Gt
  [LinearOrder α]
  {a b : α}
-- given
  (h₀ : a ≠ b)
  (h₁ : a ≥ b) :
-- imply
  a > b := by
-- proof
  by_contra h'
  simp at h'
  have h'' := Ge.Le.to.Eq h₁ h'
  contradiction


end Algebra.Ne.Ge.to

-- created on 2024-11-29
