import Axiom.Basic

namespace Algebra.Le_Length.to.Eq_.LengthDrop

theorem SubLength
  {s: List α}
  {i : Nat}
-- given
  (h: i ≤ s.length) :
-- imply
  (s.drop i |>.length) = s.length - i := by
-- proof
  induction s generalizing i
  case nil =>
    simp [List.drop]
  case cons =>
    cases i with
    | zero =>
      simp [List.drop]
    | succ i =>
      simp [List.drop]

end Algebra.Le_Length.to.Eq_.LengthDrop

-- created on 2024-07-01
