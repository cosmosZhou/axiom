import Axiom.Algebra.Gt.to.Ne
import Axiom.Algebra.Ne_.Length.Zero.Ne_0.to.Eq_.Prod.Mul_ProdTail

namespace Algebra.Gt_.Length.Zero.Gt_0.to.Eq_.Prod

theorem Mul_ProdTail
  {shape : List ℕ}
-- given
  (h1: shape.length > 0)
  (h2: shape[0] > 0) :
-- imply
  shape.prod = shape[0] * shape.tail.prod := by
-- proof
  have h1' := Gt.to.Ne h1
  have h2' := Gt.to.Ne h2

  apply Ne_.Length.Zero.Ne_0.to.Eq_.Prod.Mul_ProdTail h1' h2'

end Algebra.Gt_.Length.Zero.Gt_0.to.Eq_.Prod

-- created on 2024-07-01
