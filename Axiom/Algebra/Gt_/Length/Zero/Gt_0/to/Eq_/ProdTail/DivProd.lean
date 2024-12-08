import Axiom.Algebra.Gt.to.Ne
import Axiom.Algebra.Ne_.Length.Zero.Ne_0.to.Eq_.ProdTail.DivProd

namespace Algebra.Gt_.Length.Zero.Gt_0.to.Eq_.ProdTail

theorem DivProd
  {shape : List ℕ}
-- given
  (h1: shape.length > 0)
  (h2: shape[0] > 0) :
-- imply
  shape.tail.prod = shape.prod / shape[0] :=
-- proof
  Ne_.Length.Zero.Ne_0.to.Eq_.ProdTail.DivProd
    (Gt.to.Ne h1)
    (Gt.to.Ne h2)


end Algebra.Gt_.Length.Zero.Gt_0.to.Eq_.ProdTail

-- created on 2024-07-01
