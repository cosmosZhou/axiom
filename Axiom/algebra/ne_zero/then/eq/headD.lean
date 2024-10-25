import Mathlib.Tactic

namespace algebra.ne_zero.then.eq

theorem headD
  {s : List α}
-- given
  {default : α}
  (h : s.length ≠ 0):
-- imply
  s.headD default = s[0] := by
-- proof
  cases s with
  | nil =>
    contradiction
  | cons hd tl =>
    simp


end algebra.ne_zero.then.eq
open algebra.ne_zero.then.eq
