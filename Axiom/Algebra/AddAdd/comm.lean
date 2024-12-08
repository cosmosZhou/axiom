import Axiom.Algebra.Add.comm
import Axiom.Algebra.Add_Add.eq.AddAdd
namespace Algebra.AddAdd

theorem comm
  [AddCommSemigroup α]
  {a b : α} :
-- imply
  a + b + c = a + c + b := by
-- proof
  rw [Add.comm (b := c)]
  rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]


end Algebra.AddAdd

-- created on 2024-11-28
