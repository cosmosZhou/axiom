import Mathlib.Tactic
import Axiom.sympy.core.containers.list

namespace algebra.le_length.then.eq.length

theorem substr
  {s : List α}
  {i n : Nat}
-- given
  (h : i + n ≤ s.length) :
-- imply
  (s.substr i n |>.length) = n := by
-- proof
  simp [List.substr]
  have h'' : i + n - i ≤ s.length - i := by
    apply Nat.sub_le_sub_right h i
  rw [add_comm] at h''
  -- h'' : n + i - i ≤ s.length - i
  rw [Nat.add_sub_cancel] at h''
  exact h''


end algebra.le_length.then.eq.length
open algebra.le_length.then.eq.length
