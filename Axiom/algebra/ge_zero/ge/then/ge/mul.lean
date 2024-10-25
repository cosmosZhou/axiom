import Mathlib.Tactic
import Axiom.algebra.ge.then.le.reverse
import Axiom.algebra.ge_zero.le.then.le.mul
import Axiom.algebra.le.then.ge.reverse

namespace algebra.ge_zero.ge.then.ge

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a ≥ b):
-- imply
  x * a ≥ x * b := by
-- proof
  have h := algebra.ge.then.le.reverse h2
  have h := algebra.ge_zero.le.then.le.mul h1 h
  apply algebra.le.then.ge.reverse h


end algebra.ge_zero.ge.then.ge
open algebra.ge_zero.ge.then.ge
