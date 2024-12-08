import Axiom.Basic


namespace Algebra.AndNot.to

theorem False
-- given
  (h : ¬p ∧ p) :
-- imply
  False :=
-- proof
  h.left h.right


end Algebra.AndNot.to

-- created on 2024-07-01
