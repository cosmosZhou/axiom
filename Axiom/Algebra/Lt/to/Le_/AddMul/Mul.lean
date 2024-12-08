import Axiom.Algebra.Le.Ge_0.to.LeMulS
import Axiom.Algebra.Lt.to.LeAdd_1.nat
import Axiom.Algebra.MulAdd.eq.AddMulS

namespace Algebra.Lt.to.Le_.AddMul

theorem Mul
  {m i : ℕ}
-- given
  (h : i < m)
  (n : ℕ) :
-- imply
  i * n + n ≤ m * n := by
-- proof
  have h := Le.Ge_0.to.LeMulS
    (Lt.to.LeAdd_1.nat h)
    (show n >= 0 by simp)

  rw [MulAdd.eq.AddMulS] at h
  simp at h
  exact h


end Algebra.Lt.to.Le_.AddMul

-- created on 2024-07-01
