import Axiom.Basic

namespace Algebra.HeadDMap.eq

@[simp]
theorem FunHeadD
  {s : List α}
  {f : α → β}
  {default : α} :
-- imply
  (s.map f).headD (f default) = f (s.headD default) := by
-- proof
  simp


end Algebra.HeadDMap.eq

-- created on 2024-07-01
