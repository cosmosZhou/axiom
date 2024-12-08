import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul_Neg.eq.NegMul
namespace Algebra.Mul_Neg.eq

theorem NegSquare
  [Ring α]
  {a : α} :
-- imply
  a * -a = -a² := by
-- proof
  rw [Mul_Neg.eq.NegMul]
  rw [Mul.eq.Square]


end Algebra.Mul_Neg.eq

-- created on 2024-11-29
