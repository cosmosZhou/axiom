import Mathlib.Tactic

namespace algebra.eq.then.eq

theorem div
  {α : Type*} [Div α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  x / d = y / d :=
-- proof
by
  -- Rewrite the goal using the hypotheses
  rw [h]

end algebra.eq.then.eq
open algebra.eq.then.eq
