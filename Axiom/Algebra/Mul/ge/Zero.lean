import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Square.ge.Zero

namespace Algebra.Mul.ge

theorem Zero
  [Semiring α] [LinearOrder α]
  [IsRightCancelAdd α] [ZeroLEOneClass α] [ExistsAddOfLE α]
  [PosMulMono α] [AddLeftStrictMono α]
  {a : α} :
-- imply
  a * a ≥ 0 := by
-- proof
  rw [Mul.eq.Square]
  apply Square.ge.Zero


end Algebra.Mul.ge

-- created on 2024-11-29
