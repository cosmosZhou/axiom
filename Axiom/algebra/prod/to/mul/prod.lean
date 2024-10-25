import Mathlib.Tactic

namespace algebra.prod.to.mul

theorem prod
  [Monoid M]
  {l : List M} :
-- imply
  l.prod = l.headD 1 * l.tail.prod := by
-- proof
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]


end algebra.prod.to.mul
open algebra.prod.to.mul
