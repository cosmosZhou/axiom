import Axiom.Algebra.Lt.to.LeAdd_1.nat

namespace Algebra.Gt.to.Ge_Add_1

theorem nat
  {x y : ℕ}
-- given
  (h : x > y) :
-- imply
  x ≥ y + 1 := by
-- proof
  apply Lt.to.LeAdd_1.nat h


end Algebra.Gt.to.Ge_Add_1

-- created on 2024-07-01
