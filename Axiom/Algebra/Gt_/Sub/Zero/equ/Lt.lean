import Axiom.Basic

namespace Algebra.Gt_.Sub.Zero.equ

theorem Lt
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α} :
-- imply
  b - a > 0 ↔ a < b :=
-- proof
  sub_pos


end Algebra.Gt_.Sub.Zero.equ

-- created on 2024-11-25
