import Mathlib.Tactic

namespace algebra.ne_zero.then.eq.cons

theorem tail
  {shape : List α}
-- given
  (h: shape.length ≠ 0) :
-- imply
  shape = shape[0]::shape.tail := by
-- proof
  cases shape with
  | nil =>
    -- If shape is nil, then its length is 0, which contradicts h.
    contradiction
  | cons head tail =>
    -- If shape is cons head tail, then we need to show that shape = head :: tail.
    -- This is trivially true by definition of cons.
    rfl

end algebra.ne_zero.then.eq.cons
open algebra.ne_zero.then.eq.cons
