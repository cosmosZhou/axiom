import Axiom.Basic
import Axiom.Algebra.And.to.And.symm

namespace Algebra.And

theorem comm :
-- imply
  p ∧ q ↔ q ∧ p :=
-- proof
  ⟨
    And.to.And.symm,
    And.to.And.symm
  ⟩



end Algebra.And

-- created on 2024-07-01
