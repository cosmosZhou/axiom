import Axiom.sympy.core.numbers

namespace Algebra.Eq

@[simp]
theorem CubeCubic
  {x : ℂ} :
-- imply
  x = (∛x)³ := by
  simp [Root.cubic]



end Algebra.Eq

-- created on 2024-07-01
