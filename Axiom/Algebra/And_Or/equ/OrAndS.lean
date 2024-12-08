import Axiom.Algebra.OrAndS.to.And_Or
import Axiom.Algebra.And_Or.to.OrAndS

namespace Algebra.And_Or.equ

theorem OrAndS :
-- imply
  p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r :=
-- proof
  ⟨And_Or.to.OrAndS, OrAndS.to.And_Or⟩


end Algebra.And_Or.equ

-- created on 2024-07-01
