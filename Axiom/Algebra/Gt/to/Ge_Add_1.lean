import Axiom.Algebra.Lt.to.LeAdd_1

namespace Algebra.Gt.to

theorem Ge_Add_1
  {x y : ℤ}
-- given
  (h : x > y) :
-- imply
  x ≥ y + 1 :=
-- proof
  Lt.to.LeAdd_1 h


end Algebra.Gt.to

-- created on 2024-07-01
