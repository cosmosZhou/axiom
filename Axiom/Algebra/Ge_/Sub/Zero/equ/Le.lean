import Axiom.Basic


namespace Algebra.Ge_.Sub.Zero.equ

theorem Le
  [AddGroup α] [LE α] [AddRightMono α]
  {a b : α} :
-- imply
  b - a ≥ 0 ↔ a ≤ b :=
-- proof
  sub_nonneg


end Algebra.Ge_.Sub.Zero.equ

-- created on 2024-11-25
