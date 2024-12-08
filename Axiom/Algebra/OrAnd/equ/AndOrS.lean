import Axiom.Algebra.OrAnd.to.AndOrS
import Axiom.Algebra.AndOrS.to.OrAnd

namespace Algebra.OrAnd.equ

theorem AndOrS :
-- imply
  p ∧ q ∨ r ↔ (p ∨ r) ∧ (q ∨ r) :=
-- proof
  ⟨OrAnd.to.AndOrS, AndOrS.to.OrAnd⟩


end Algebra.OrAnd.equ

-- created on 2024-07-01
