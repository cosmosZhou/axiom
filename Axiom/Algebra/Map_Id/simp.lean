import Axiom.Basic
open Mathlib
namespace Algebra.Map_Id

@[simp]
theorem simp
  {s : Vector α n} :
-- imply
  s.map (fun x => x) = s := by
-- proof
  apply Vector.map_id


end Algebra.Map_Id

-- created on 2024-07-01
