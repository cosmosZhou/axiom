import Axiom.Basic

namespace Algebra.Ne_.Length.Zero.to

theorem EqHeadD
  {s : List α}
  {default : α}
-- given
  (h : s.length ≠ 0) :
-- imply
  s.headD default = s[0] := by
-- proof
  cases s with
  | nil =>
    contradiction
  | cons hd tl =>
    simp


end Algebra.Ne_.Length.Zero.to

-- created on 2024-07-01
