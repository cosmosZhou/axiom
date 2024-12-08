import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.Le.to.LeAddS
namespace Algebra.Le.to

theorem LeSubS
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x ≤ y)
  (z : α) :
-- imply
  x - z ≤ y - z := by
-- proof
  rw [Sub.eq.Add_Neg (a := x), Sub.eq.Add_Neg (a := y)]
  apply Le.to.LeAddS h (-z)


end Algebra.Le.to

-- created on 2024-07-01
