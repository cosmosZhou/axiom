import Axiom.sympy.core.containers.list
import Axiom.Algebra.Add.comm

namespace Algebra.Le_.Add.Length.to

theorem EqLengthSubstr
  {s : List α}
  {i n : Nat}
-- given
  (h : i + n ≤ s.length) :
-- imply
  (s.substr i n |>.length) = n := by
-- proof
  simp [List.substr]
  have h'' : i + n - i ≤ s.length - i := Nat.sub_le_sub_right h i
  rw [Add.comm] at h''
  -- h'' : n + i - i ≤ s.length - i
  rw [Nat.add_sub_cancel] at h''
  exact h''


end Algebra.Le_.Add.Length.to

-- created on 2024-07-01
