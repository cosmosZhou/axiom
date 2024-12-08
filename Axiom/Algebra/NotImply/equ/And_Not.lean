import Axiom.Algebra.NotImply.to.And_Not
import Axiom.Algebra.And_Not.to.NotImply

namespace Algebra.NotImply.equ

theorem And_Not :
-- imply
  ¬(p → q) ↔ p ∧ ¬q :=
-- proof
  ⟨NotImply.to.And_Not, And_Not.to.NotImply⟩


end Algebra.NotImply.equ

-- created on 2024-07-01
