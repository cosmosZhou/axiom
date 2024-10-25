import Mathlib.Tactic
set_option linter.dupNamespace false

namespace algebra.headD.map.fn.to.fn


theorem headD
  {s : List α}
  {f : α → β}
  {default : α}:
-- imply
  (s.map f).headD (f default) = f (s.headD default) := by
  simp
  -- cases s with
  -- | nil => simp
  -- | cons h t => simp

  -- match s with
  -- | List.nil => simp
  -- | List.cons h t => simp


end algebra.headD.map.fn.to.fn
open algebra.headD.map.fn.to.fn
