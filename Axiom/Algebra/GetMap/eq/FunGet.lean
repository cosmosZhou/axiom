import Axiom.Basic
open Mathlib
namespace Algebra.GetMap.eq

@[simp]
theorem FunGet
  (v : Vector α n)
  (f : α → β)
  (i : Fin n) :
-- imply
  (v.map f).get i = f (v.get i) := by
-- proof
  simp [Vector.get_map]


end Algebra.GetMap.eq

-- created on 2024-07-01
