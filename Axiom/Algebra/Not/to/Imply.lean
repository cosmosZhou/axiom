import Axiom.Basic


namespace Algebra.Not.to

theorem Imply
  {p q : Prop}
-- given
  (h : ¬p) :
-- imply
  p → q := by
-- proof
  intro hp
  contradiction


end Algebra.Not.to

-- created on 2024-07-01
