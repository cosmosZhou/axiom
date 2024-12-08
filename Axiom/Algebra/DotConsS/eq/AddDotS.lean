import Axiom.sympy.core.containers.vector
open Mathlib

namespace Algebra.DotConsS.eq

theorem AddDotS
  [Add α] [Zero α] [Mul α]
  {a a' : α}
  {s s' : Vector α n} :
-- imply
  (a ::ᵥ s) ⬝ (a' ::ᵥ s') = a * a' + s ⬝ s' := by
-- proof
  simp [Vector.dot]

end Algebra.DotConsS.eq

-- created on 2024-07-01
