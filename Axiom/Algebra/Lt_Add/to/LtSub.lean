import Axiom.Algebra.GtAdd.to.Gt_Sub

namespace Algebra.Lt_Add.to

theorem LtSub
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c < a + b) :
-- imply
  c - b < a :=
-- proof
  GtAdd.to.Gt_Sub h


end Algebra.Lt_Add.to

-- created on 2024-11-27
