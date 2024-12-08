import Axiom.Algebra.Ge_.Sub.Zero.equ.Le


namespace Algebra.Le.to.Sub.ge

theorem Zero
  [AddGroup α] [LE α] [AddRightMono α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  b - a ≥ 0 :=
-- proof
  -- apply
  Ge_.Sub.Zero.equ.Le.mpr h


end Algebra.Le.to.Sub.ge

-- created on 2024-11-25
