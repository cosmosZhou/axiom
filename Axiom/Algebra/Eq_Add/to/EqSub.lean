import Axiom.Algebra.EqAdd.to.Eq_Sub

namespace Algebra.Eq_Add.to

theorem EqSub
  [AddGroup α]
  {x y d : α}
-- given
  (h : y = d + x) :
-- imply
  y - x = d :=
-- proof
  (EqAdd.to.Eq_Sub h.symm).symm


end Algebra.Eq_Add.to

-- created on 2024-11-27
