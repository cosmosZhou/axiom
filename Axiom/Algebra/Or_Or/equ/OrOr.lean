import Axiom.Basic
import Axiom.Algebra.OrOr.equ.Or_Or

namespace Algebra.Or_Or.equ

theorem OrOr :
-- imply
  p ∨ q ∨ r ↔ (p ∨ q) ∨ r :=
-- proof
  OrOr.equ.Or_Or.symm


end Algebra.Or_Or.equ

-- created on 2024-07-01
