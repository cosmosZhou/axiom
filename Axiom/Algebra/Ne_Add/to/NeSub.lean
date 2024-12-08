import Axiom.Algebra.NeAdd.to.Ne_Sub

namespace Algebra.Ne_Add.to

theorem NeSub
  [AddGroup α]
  {x a b: α}
-- given
  (h : a ≠ x + b) :
-- imply
  a - b ≠ x :=
-- proof
  (NeAdd.to.Ne_Sub h.symm).symm


end Algebra.Ne_Add.to

-- created on 2024-11-27
