import Mathlib.Tactic
import Axiom.algebra.ge_zero.le.then.le.mul
import Axiom.algebra.gt.then.ge.relax

namespace algebra.gt_zero.ge.then.ge

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x > 0)
  (h2 : a ≥ b):
-- imply
  x * a ≥ x * b := by
-- proof
  have h := algebra.gt.then.ge.relax h1
  apply algebra.ge_zero.le.then.le.mul h h2



end algebra.gt_zero.ge.then.ge
open algebra.gt_zero.ge.then.ge
