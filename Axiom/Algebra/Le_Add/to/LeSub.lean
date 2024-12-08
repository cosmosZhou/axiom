import Axiom.Algebra.GeAdd.to.Ge_Sub

namespace Algebra.Le_Add.to

theorem LeSub
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c ≤ a + b) :
-- imply
  c - b ≤ a :=
-- proof
  GeAdd.to.Ge_Sub h


end Algebra.Le_Add.to

-- created on 2024-11-27
