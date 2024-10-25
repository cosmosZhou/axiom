import Mathlib.Tactic

namespace algebra.lt.then.add_le.st.one

theorem nat
  {x y : ℕ}
-- given
  (h : x < y):
-- imply
  x + 1 ≤ y := by
-- proof
  apply Nat.succ_le_of_lt h


end algebra.lt.then.add_le.st.one
open algebra.lt.then.add_le.st.one
