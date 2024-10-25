import Mathlib.Tactic
set_option linter.dupNamespace false


namespace algebra.eq.eq.then.eq

theorem subs
  {a b c : ℂ}
-- given
  (h1 : a = 2 * c)
  (h2 : a * b = d) :
-- imply
  2 * b * c = d :=
-- proof
by
  rw [h1] at h2
  -- h2: 2 * c * b = d
  rw [mul_assoc] at h2
  -- h2: 2 * (c * b) = d
  rw [mul_comm c b] at h2
  -- h2: 2 * (b * c) = d
  rw [mul_assoc]
  exact h2

end algebra.eq.eq.then.eq
open algebra.eq.eq.then.eq
