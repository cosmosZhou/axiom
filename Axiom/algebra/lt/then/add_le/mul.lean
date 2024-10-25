import Mathlib.Tactic
import Axiom.algebra.lt.then.add_le.st.one.nat
import Axiom.algebra.le.ge_zero.then.le.mul
import Axiom.algebra.mul.to.add.distrib.right
import Axiom.algebra.one_mul.simp

namespace algebra.lt.then.add_le

theorem mul
  {m i : ℕ}
-- given
  (h : i < m)
  (n : ℕ):
-- imply
  i * n + n ≤ m * n := by
-- proof
  have h := algebra.lt.then.add_le.st.one.nat h
  have h' : n >= 0 := by simp
  have h := algebra.le.ge_zero.then.le.mul h h'

  rw [
    algebra.mul.to.add.distrib.right,
    algebra.one_mul.simp
  ] at h
  exact h


end algebra.lt.then.add_le
open algebra.lt.then.add_le
