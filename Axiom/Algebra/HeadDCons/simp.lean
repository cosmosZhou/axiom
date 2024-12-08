import Axiom.sympy.core.containers.vector
open Mathlib
namespace Algebra.HeadDCons


@[simp]
theorem simp
  {s : Vector α n}
  {default : α} :
-- imply
  (a ::ᵥ s).headD default = a := by
-- proof
  rfl

end Algebra.HeadDCons

-- created on 2024-07-01
