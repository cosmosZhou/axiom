import Axiom.Algebra.Lt.to.LtSubS

namespace Algebra.Gt.to

theorem GtSubS
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x > y)
  (z : α) :
-- imply
  x - z > y - z :=
-- proof
  Lt.to.LtSubS h z


end Algebra.Gt.to

-- created on 2024-07-01
