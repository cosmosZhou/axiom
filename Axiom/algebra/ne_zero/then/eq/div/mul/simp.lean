import Mathlib.Tactic

namespace algebra.ne_zero.then.eq.div.mul

theorem simp
-- given
  {a : ℂ}
  (h : a ≠ 0)
  (b : ℂ) :
-- imply
  a * b / a = b := by
-- proof
  simp [h]
  -- rw [div_eq_mul_inv]
  -- -- Now we have `a * b * a⁻¹`
  -- rw [mul_comm a b]
  -- -- Now we have `b * a * a⁻¹`
  -- rw [mul_assoc]
  -- -- Now we have `b * (a * a⁻¹)`
  -- rw [mul_inv_cancel h]
  -- rw [mul_one]

end algebra.ne_zero.then.eq.div.mul
open algebra.ne_zero.then.eq.div.mul
