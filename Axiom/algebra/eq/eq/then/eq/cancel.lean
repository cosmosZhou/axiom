import Mathlib.Tactic
set_option linter.dupNamespace false

namespace algebra.eq.eq.then.eq

theorem cancel
  {a b c d x : ℂ}
  {hc : c ≠ 0}
  {hd : d ≠ 0}
-- given
  (a_def : a = c * x)
  (b_def : b = d * x) :
-- imply
  b / d = a / c :=
-- proof
by calc
  b / d = d * x / d := by rw [b_def]
      _ = x         := by simp [hd]
      _ = c * x / c := by simp [hc]
      _ = a / c     := by rw [a_def]


end algebra.eq.eq.then.eq
open algebra.eq.eq.then.eq
