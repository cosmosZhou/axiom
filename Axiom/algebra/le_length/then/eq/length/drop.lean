import Mathlib.Tactic
set_option linter.dupNamespace false

namespace algebra.le_length.then.eq.length

theorem drop
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

end algebra.le_length.then.eq.length
open algebra.le_length.then.eq.length
