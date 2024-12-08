import Axiom.sympy.core.numbers

namespace Algebra.SquareSqrt

@[simp]
theorem simp
  {x : ℂ} :
-- imply
  (√x)² = x := by
  simp [Root.sqrt]


end Algebra.SquareSqrt

-- created on 2024-07-01
