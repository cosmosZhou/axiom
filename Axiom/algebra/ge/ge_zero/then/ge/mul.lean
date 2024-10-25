import Mathlib.Tactic
import Axiom.algebra.le.ge_zero.then.le.mul
import Axiom.algebra.ge.then.le.reverse
import Axiom.algebra.le.then.ge.reverse

namespace algebra.ge.ge_zero.then.ge

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a ≥ b)
  (h2 : x ≥ 0):
-- imply
  a * x ≥ b * x := by
-- proof
  have h := algebra.ge.then.le.reverse h1
  have h := algebra.le.ge_zero.then.le.mul h h2
  apply algebra.le.then.ge.reverse h


end algebra.ge.ge_zero.then.ge
open algebra.ge.ge_zero.then.ge
