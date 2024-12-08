import Axiom.Basic

namespace Algebra.LengthJoin.eq

theorem SumMap_FunLength
  {s : List (List α)} :
-- imply
  s.join.length = (s.map fun s => s.length).sum := by
-- proof
  induction s with
    | nil =>
      -- Base case: s = []
      simp [List.join]
    | cons head tail _ =>
      -- Inductive case: s = head :: tail
      simp [List.join]

end Algebra.LengthJoin.eq

-- created on 2024-07-01
