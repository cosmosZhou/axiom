import Axiom.Basic

namespace Algebra.Lt.to.LeAdd_1

theorem nat
  {x y : ℕ}
-- given
  (h : x < y) :
-- imply
  x + 1 ≤ y :=
-- proof
  Nat.succ_le_of_lt h


end Algebra.Lt.to.LeAdd_1

-- created on 2024-07-01
