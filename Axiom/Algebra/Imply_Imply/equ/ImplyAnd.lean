import Axiom.Algebra.Imply.equ.OrNot
import Axiom.Algebra.NotAnd.equ.OrNotS
import Axiom.Algebra.OrOr.equ.Or_Or

namespace Algebra.Imply_Imply.equ

theorem ImplyAnd :
-- imply
  p → q → r ↔ p ∧ q → r := by
-- proof
  rw [
    Imply.equ.OrNot,
    Imply.equ.OrNot,
    Imply.equ.OrNot,
    NotAnd.equ.OrNotS,
    OrOr.equ.Or_Or
  ]


end Algebra.Imply_Imply.equ

-- created on 2024-07-01
