import Axiom.Basic

namespace Algebra.Ne.to.Ne

theorem symm
  {α : Type*}
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a := by
-- proof
  exact h.symm


end Algebra.Ne.to.Ne

-- created on 2024-07-01
