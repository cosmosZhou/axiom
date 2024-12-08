import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Ge_0.to.Neg.le.Zero

namespace Algebra.NegSquare.le

theorem Zero
  [LinearOrderedRing α]
  {a : α} :
-- imply
  -a² ≤ 0 := by
-- proof
  have h := Square.ge.Zero (a := a)
  apply Ge_0.to.Neg.le.Zero h


end Algebra.NegSquare.le

-- created on 2024-11-29
