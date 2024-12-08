import Axiom.Algebra.Ne_.Length.Zero.Ne_0.to.Eq_.Prod.Mul_ProdTail
import Axiom.Algebra.Eq.to.EqDivS

namespace Algebra.Ne_.Length.Zero.Ne_0.to.Eq_.ProdTail

theorem DivProd
  {shape : List ℕ}
-- given
  (h1: shape.length ≠ 0)
  (h2: shape[0] ≠ 0) :
-- imply
  shape.tail.prod = shape.prod / shape[0] := by
-- proof
  -- Use the product property
  have h_prod := Ne_.Length.Zero.Ne_0.to.Eq_.Prod.Mul_ProdTail h1 h2

  -- divide both sides by shape[0]
  have h_div : shape.prod / shape[0] = shape[0] * shape.tail.prod / shape[0] := by
    apply Eq.to.EqDivS h_prod shape[0]

  simp [h2] at h_div
  -- h_div : shape.prod / shape[0] = shape.tail.prod
  exact h_div.symm

end Algebra.Ne_.Length.Zero.Ne_0.to.Eq_.ProdTail

-- created on 2024-07-01
