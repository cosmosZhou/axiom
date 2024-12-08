import Axiom.Algebra.LtAdd.to.Lt_Sub

namespace Algebra.Gt_Add.to

theorem GtSub
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c > a + b) :
-- imply
  c - b > a :=
-- proof
  LtAdd.to.Lt_Sub h


end Algebra.Gt_Add.to

-- created on 2024-11-27
