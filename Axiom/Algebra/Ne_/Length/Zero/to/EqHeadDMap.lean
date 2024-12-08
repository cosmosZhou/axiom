import Axiom.Basic

namespace Algebra.Ne_.Length.Zero.to

theorem EqHeadDMap
  {s : List α}
  {default : β}
  {f : α → β}
-- given
  (h : s.length ≠ 0) :
-- imply
  (s.map f).headD default = f s[0] := by
-- proof
  cases s with
  | nil =>
    contradiction
  | cons hd tl =>
    simp


end Algebra.Ne_.Length.Zero.to

-- created on 2024-07-01
