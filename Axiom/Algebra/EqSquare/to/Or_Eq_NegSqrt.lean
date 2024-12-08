import Axiom.sympy.core.numbers
import Axiom.Algebra.SquareSqrt.simp
import Axiom.Algebra.EqSquareS.to.OrEqS

namespace Algebra.EqSquare.to

theorem Or_Eq_NegSqrt
  {x c : ℂ}
-- given
  (h : x ^ 2 = c) :
-- imply
  x = √c ∨ x = -√c := by
-- proof
  let t := √c
  have h_t : t ^ 2 = c := SquareSqrt.simp

  exact EqSquareS.to.OrEqS (h_t.symm ▸ h)

end Algebra.EqSquare.to

-- created on 2024-07-01
