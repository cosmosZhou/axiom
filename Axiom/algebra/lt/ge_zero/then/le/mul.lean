import Mathlib.Tactic
import Axiom.algebra.lt.then.le.relax
import Axiom.algebra.le.ge_zero.then.le.mul

namespace algebra.lt.ge_zero.then.le

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a < b)
  (h2 : x ≥ 0):
-- imply
  a * x ≤ b * x := by
-- proof
  have h := algebra.lt.then.le.relax h1
  apply algebra.le.ge_zero.then.le.mul h h2


end algebra.lt.ge_zero.then.le
open algebra.lt.ge_zero.then.le
