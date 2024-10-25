import Mathlib.Tactic

namespace algebra.length.join.to.sum

theorem map
  {s : List (List α)}:
  s.join.length = (s.map fun s => s.length).sum := by
  induction s with
    | nil =>
      -- Base case: s = []
      simp [List.join]
    | cons head tail _ =>
      -- Inductive case: s = head :: tail
      simp [List.join]

end algebra.length.join.to.sum
open algebra.length.join.to.sum
