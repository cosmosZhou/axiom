import Mathlib.Tactic

namespace algebra.prod.cons.to.mul

theorem prod
  [Monoid M]
  {l : List M} {a : M} :
-- imply
  (a :: l).prod = a * l.prod := by
-- proof
  apply List.prod_cons


end algebra.prod.cons.to.mul
open algebra.prod.cons.to.mul
