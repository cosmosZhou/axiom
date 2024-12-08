import Axiom.Algebra.GetMap.eq.FunGet
open Mathlib
namespace Algebra.Map.eq

theorem Replicate
  {s : Vector α n}
  {default : α} :
-- imply
  (s.map fun _ => default) = Vector.replicate n default := by
-- proof
  apply Vector.ext
  intro i
  simp [GetMap.eq.FunGet]


end Algebra.Map.eq

-- created on 2024-07-01
