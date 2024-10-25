import Mathlib.Tactic
import Axiom.algebra.gt.then.ge.relax
import Axiom.algebra.ge_zero.ge.then.ge.mul

namespace algebra.ge_zero.gt.then.ge

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a > b):
-- imply
  x * a ≥ x * b := by
-- proof
  have h := algebra.gt.then.ge.relax h2
  apply algebra.ge_zero.ge.then.ge.mul h1 h


end algebra.ge_zero.gt.then.ge
open algebra.ge_zero.gt.then.ge
