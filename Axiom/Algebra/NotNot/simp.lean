import Axiom.Basic


namespace Algebra.NotNot

-- 双否定律: double-negation elimination
@[simp]
theorem simp
  {p : Prop} :
-- imply
  ¬¬p ↔ p := by
-- proof
  simp
  -- by_contra h_not_p  -- Assume ¬p
  -- exact h h_not_p    -- Apply h to ¬p


end Algebra.NotNot

-- created on 2024-07-01
