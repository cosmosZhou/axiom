import Axiom.Algebra.OrNotS.to.NotAnd
import Axiom.Algebra.NotAnd.to.OrNotS
namespace Algebra.OrNotS.equ

theorem NotAnd :
-- imply
  ¬p ∨ ¬q ↔ ¬(p ∧ q) :=
-- proof
  ⟨OrNotS.to.NotAnd,  NotAnd.to.OrNotS⟩


end Algebra.OrNotS.equ

-- created on 2024-07-01
