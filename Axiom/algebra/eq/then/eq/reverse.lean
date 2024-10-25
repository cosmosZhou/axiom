import Mathlib.Tactic

namespace algebra.eq.then.eq

theorem reverse
  {α : Type*}
  {a b : α}
-- given
  (h : a = b) :
-- imply
  b = a := by
-- proof
  apply Eq.symm h


end algebra.eq.then.eq
open algebra.eq.then.eq
