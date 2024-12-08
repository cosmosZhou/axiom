import Axiom.sympy.core.numbers

namespace Algebra.Square.ge

theorem Zero
  [Semiring α] [LinearOrder α]
  [IsRightCancelAdd α] [ZeroLEOneClass α] [ExistsAddOfLE α]
  [PosMulMono α] [AddLeftStrictMono α]
  {a : α} :
-- imply
  a² ≥ 0:= by
-- proof
  apply sq_nonneg


end Algebra.Square.ge

-- created on 2024-11-29
