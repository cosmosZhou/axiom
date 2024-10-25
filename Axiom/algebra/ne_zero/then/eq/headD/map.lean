import Mathlib.Tactic

namespace algebra.ne_zero.then.eq.headD

theorem map
  {s : List α}
  {default : β}
  {f : α → β}
-- given
  (h : s.length ≠ 0):
-- imply
  (s.map f).headD default = f s[0] := by
-- proof
  cases s with
  | nil =>
    -- simp [map]
    contradiction
  | cons hd tl =>
    -- simp [map]
    simp


end algebra.ne_zero.then.eq.headD
open algebra.ne_zero.then.eq.headD
