import Axiom.Basic

namespace Algebra.SumCons.eq

theorem Add_Sum
  [Add α] [Zero α]
  {l : List α} {a : α} :
-- imply
  (a :: l).sum = a + l.sum :=
-- proof
  List.sum_cons


end Algebra.SumCons.eq

-- created on 2024-07-01
