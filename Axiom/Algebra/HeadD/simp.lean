import Axiom.sympy.core.containers.vector
open Mathlib
namespace Algebra.HeadD


@[simp]
theorem simp
  {s : Vector α 0}
  {default : α} :
-- imply
  s.headD default = default := by
-- proof
  match s with
  | Vector.nil => rfl

end Algebra.HeadD

-- created on 2024-07-01
