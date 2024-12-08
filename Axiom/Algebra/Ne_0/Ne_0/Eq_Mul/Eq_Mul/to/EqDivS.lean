import Axiom.Basic

namespace Algebra.Ne_0.Ne_0.Eq_Mul.Eq_Mul.to

theorem EqDivS
  {a b c d x : ℂ}
-- given
  (hc : c ≠ 0)
  (hd : d ≠ 0)
  (a_def : a = c * x)
  (b_def : b = d * x) :
-- imply
  b / d = a / c := by
-- proof
  calc
  b / d = d * x / d := by rw [b_def]
      _ = x         := by simp [hd]
      _ = c * x / c := by simp [hc]
      _ = a / c     := by rw [a_def]


end Algebra.Ne_0.Ne_0.Eq_Mul.Eq_Mul.to

-- created on 2024-07-01
