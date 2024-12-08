import Axiom.Algebra.Gt_.Sub.Zero.equ.Lt

namespace Algebra.Lt.to.Sub.gt

theorem Zero
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  b - a > 0 :=
-- proof
  -- apply
  Gt_.Sub.Zero.equ.Lt.mpr h


end Algebra.Lt.to.Sub.gt

-- created on 2024-11-25
