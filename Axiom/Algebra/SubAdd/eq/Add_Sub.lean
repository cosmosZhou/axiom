import Axiom.Basic
import Axiom.Algebra.Add_Sub.eq.SubAdd

namespace Algebra.SubAdd.eq

theorem Add_Sub
  [SubNegMonoid α]
  {a b c : α} :
-- imply
  a + b - c = a + (b - c) := by
-- proof
  rw [Add_Sub.eq.SubAdd]


end Algebra.SubAdd.eq

-- created on 2024-07-01
