import Axiom.Algebra.EqAdd.to.Eq_Sub

namespace Algebra.Eq_.Add.Zero.to


theorem Eq_Neg
  [AddGroup α]
  {x d : α}
-- given
  (h : x + d = 0) :
-- imply
  x = -d := by
-- proof
  simp [EqAdd.to.Eq_Sub h]


end Algebra.Eq_.Add.Zero.to

-- created on 2024-07-01
