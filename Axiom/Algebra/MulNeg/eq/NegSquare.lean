import Axiom.Algebra.MulNeg.eq.NegMul
import Axiom.Algebra.Mul.eq.Square

namespace Algebra.MulNeg.eq

theorem NegSquare
  [Ring α]
  {a : α} :
-- imply
  -a * a = -a² := by
-- proof
  rw [
    MulNeg.eq.NegMul,
    Mul.eq.Square
  ]


end Algebra.MulNeg.eq

-- created on 2024-11-29
