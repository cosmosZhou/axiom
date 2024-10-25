import Mathlib.Tactic
import Axiom.algebra.gt.then.ge.relax
import Axiom.algebra.ge.ge_zero.then.ge.mul

namespace algebra.gt.ge_zero.then.ge

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a > b)
  (h2 : x ≥ 0):
-- imply
  a * x ≥ b * x := by
-- proof
  have h := algebra.gt.then.ge.relax h1
  apply algebra.ge.ge_zero.then.ge.mul h h2


end algebra.gt.ge_zero.then.ge
open algebra.gt.ge_zero.then.ge
