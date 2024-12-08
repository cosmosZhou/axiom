import Axiom.Algebra.Imply.to.OrNot
import Axiom.Algebra.OrNot.to.Imply

namespace Algebra.Imply.equ

theorem OrNot :
-- imply
  (p → q ↔ ¬p ∨ q)  :=
-- proof
  ⟨Imply.to.OrNot, OrNot.to.Imply⟩


end Algebra.Imply.equ

-- created on 2024-07-01
