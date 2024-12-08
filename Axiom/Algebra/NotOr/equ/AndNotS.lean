import Axiom.Algebra.NotOr.to.AndNotS
import Axiom.Algebra.AndNotS.to.NotOr

namespace Algebra.NotOr.equ

theorem AndNotS :
-- imply
  ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
-- proof
  ⟨NotOr.to.AndNotS, AndNotS.to.NotOr⟩


end Algebra.NotOr.equ

-- created on 2024-07-01
