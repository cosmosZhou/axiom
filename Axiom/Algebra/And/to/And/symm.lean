import Axiom.Basic

namespace Algebra.And.to.And

theorem symm
-- given
  (h : p ∧ q) :
-- imply
  q ∧ p :=
-- proof
  ⟨h.right, h.left⟩

end Algebra.And.to.And

-- created on 2024-07-01
