import Axiom.Algebra.Lt.to.Le_Sub_1.nat

namespace Algebra.Gt.to.GeSub_1

theorem nat
  {x y : ℕ}
-- given
  (h : x > y) :
-- imply
  x - 1 ≥ y :=
-- proof
  Lt.to.Le_Sub_1.nat h


end Algebra.Gt.to.GeSub_1

-- created on 2024-07-01
