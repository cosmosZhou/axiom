import Mathlib.Tactic

namespace algebra.ne.then.ne

theorem reverse
  {α : Type*}
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a := by
-- proof
  apply Ne.symm h


end algebra.ne.then.ne
open algebra.ne.then.ne
