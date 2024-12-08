import Axiom.Basic


namespace Algebra.Imply.to

theorem OrNot
  {p q : Prop}
-- given
  (h : p → q) :
-- imply
  ¬p ∨ q := by
-- proof
  by_cases hp : p

  -- Case 1: p is true
  right
  exact h hp

  -- Case 2: p is false
  left
  exact hp


end Algebra.Imply.to

-- created on 2024-07-01
