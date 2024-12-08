import Axiom.Basic
namespace Algebra.MatchTrueS.equ


@[simp]
theorem True
  {bool : Bool} :
-- imply
  (match bool with
| true => True
| false => True) ↔ True := by
-- proof
  cases bool
  case true =>
    simp
  case false =>
    simp


end Algebra.MatchTrueS.equ

-- created on 2024-07-01
