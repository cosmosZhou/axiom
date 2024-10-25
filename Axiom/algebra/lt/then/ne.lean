import Mathlib.Tactic

namespace algebra.lt.then

theorem ne
  {α : Type*} [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≠ y := by
-- proof
  apply ne_of_lt h


end algebra.lt.then
open algebra.lt.then
