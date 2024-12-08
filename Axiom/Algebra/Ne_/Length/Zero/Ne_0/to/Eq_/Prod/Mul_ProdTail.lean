import Axiom.Algebra.Ne_0.to.Eq_Cons_Tail
import Axiom.Algebra.ProdCons.eq.Mul_Prod

namespace Algebra.Ne_.Length.Zero.Ne_0.to.Eq_.Prod

theorem Mul_ProdTail
  {shape : List ℕ}
-- given
  (h1: shape.length ≠ 0)
  (h2: shape[0] ≠ 0) :
-- imply
  shape.prod = shape[0] * shape.tail.prod := by
-- proof
  -- Use the product property
  have h_prod : (shape[0]::shape.tail).prod = shape[0] * shape.tail.prod := by
    simp [ProdCons.eq.Mul_Prod]

  have h_cons := Ne_0.to.Eq_Cons_Tail h1

  rw [h_cons.symm] at h_prod
  exact h_prod

end Algebra.Ne_.Length.Zero.Ne_0.to.Eq_.Prod

-- created on 2024-07-01
