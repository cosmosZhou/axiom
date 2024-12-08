import Axiom.Algebra.Lt.to.LtAddS
import Axiom.Algebra.Sub.eq.Add_Neg

namespace Algebra.Lt.to

theorem LtSubS
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x < y)
  (z : α) :
-- imply
  x - z < y - z:= by
-- proof
  rw [Sub.eq.Add_Neg (a := x), Sub.eq.Add_Neg (a := y)]
  apply Lt.to.LtAddS h (-z)


end Algebra.Lt.to

-- created on 2024-07-01
