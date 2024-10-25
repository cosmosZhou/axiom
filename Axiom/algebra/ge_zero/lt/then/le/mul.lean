import Mathlib.Tactic
import Axiom.algebra.lt.then.le.relax
import Axiom.algebra.ge_zero.le.then.le.mul

namespace algebra.ge_zero.lt.then.le

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a < b):
-- imply
  x * a ≤ x * b := by
-- proof
  have h := algebra.lt.then.le.relax h2
  apply algebra.ge_zero.le.then.le.mul h1 h


end algebra.ge_zero.lt.then.le
open algebra.ge_zero.lt.then.le
