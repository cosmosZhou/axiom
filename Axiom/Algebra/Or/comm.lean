import Axiom.Basic
import Axiom.Algebra.Or.to.Or.symm

namespace Algebra.Or

theorem comm :
-- imply
  p ∨ q ↔ q ∨ p :=
-- proof
  ⟨
    Or.to.Or.symm,
    Or.to.Or.symm
  ⟩


end Algebra.Or

-- created on 2024-07-01
