import Axiom.Basic
open Mathlib
namespace Sets

theorem In_Cons
  {s : List α} :
-- imply
  x ∈ x :: s := by
-- proof
  apply List.Mem.head

end Sets
-- created on 2024-07-01
