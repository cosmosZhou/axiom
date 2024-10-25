import Mathlib.Tactic

namespace algebra.sum.cons.to.add

theorem sum
  [AddMonoid M]
  {l : List M} {a : M} :
-- imply
  (a :: l).sum = a + l.sum := by
-- proof
  apply List.sum_cons


end algebra.sum.cons.to.add
open algebra.sum.cons.to.add
