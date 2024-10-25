import Mathlib.Tactic
import Axiom.sympy.core.containers.list

namespace algebra.sum.map.fn.mul.to.dot.map


theorem fn
  [AddMonoid β] [Mul β]
  {s : List α}
  {f₁ f₂ : α → β} :
-- imply
  (s.map fun x => (f₁ x) * (f₂ x)).sum = (s.map f₁).dot (s.map f₂) := by
-- proof
  induction s with
  | nil =>
    simp [List.dot]
  | cons x xs ih =>
    simp [List.map, List.dot, ih]

end algebra.sum.map.fn.mul.to.dot.map
open algebra.sum.map.fn.mul.to.dot.map
