import Axiom.Algebra.NeSub.to.Ne_Add

namespace Algebra.Ne_Sub.to

theorem NeAdd
  [AddGroup α]
  {x a b: α}
-- given
  (h : a ≠ x - b) :
-- imply
  a + b ≠ x :=
-- proof
  (NeSub.to.Ne_Add h.symm).symm


end Algebra.Ne_Sub.to

-- created on 2024-11-27
