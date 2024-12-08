import Axiom.Algebra.Le.to.LeSubS

namespace Algebra.Ge.to

theorem GeSubS
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x ≥ y)
  (z : α) :
-- imply
  x - z ≥ y - z:=
-- proof
  Le.to.LeSubS h z


end Algebra.Ge.to

-- created on 2024-07-01
