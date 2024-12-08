import Axiom.sympy.core.containers.vector
open Mathlib

namespace Algebra.TailCons.eq.Tail

@[simp]
theorem vector
  {l : Vector α n} :
-- imply
  (a ::ᵥ l.tail).tail = l.tail := by
-- proof
  rfl

end Algebra.TailCons.eq.Tail

-- created on 2024-07-01
