import Axiom.sympy.core.containers.list
open Mathlib

namespace Algebra.TailCons.eq

@[simp]
theorem Tail
  {l : List α} :
-- imply
  (a :: l.tail).tail = l.tail := by
-- proof
  rfl

end Algebra.TailCons.eq

-- created on 2024-07-01
