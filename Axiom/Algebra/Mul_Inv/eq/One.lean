import Axiom.Basic


namespace Algebra.Mul_Inv.eq

@[simp]
theorem One
  [Group α]
  {a : α} :
-- imply
  a * a⁻¹ = 1 := by
-- proof
  apply mul_inv_cancel


end Algebra.Mul_Inv.eq

-- created on 2024-11-25
