import Axiom.Basic

namespace Algebra.Ne_0.to

theorem Eq_Cons_Tail
  {s : List α}
-- given
  (h: s.length ≠ 0) :
-- imply
  s = s[0]::s.tail := by
-- proof
  cases s with
  | nil =>
    -- If s is nil, then its length is 0, which contradicts h.
    contradiction
  | cons head tail =>
    -- If s is cons head tail, then we need to show that s = head :: tail.
    -- This is trivially true by definition of cons.
    rfl

end Algebra.Ne_0.to

-- created on 2024-07-01
