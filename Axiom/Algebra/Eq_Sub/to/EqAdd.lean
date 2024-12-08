import Axiom.Algebra.EqSub.to.Eq_Add

namespace Algebra.Eq_Sub.to

theorem EqAdd
  [AddGroup α]
  {x a b: α}
-- given
  (h : a = x - b) :
-- imply
  a + b = x :=
-- proof
  (EqSub.to.Eq_Add h.symm).symm


end Algebra.Eq_Sub.to

-- created on 2024-11-27
