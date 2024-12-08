import Axiom.Algebra.LeAdd.to.Le_Sub

namespace Algebra.Ge_Add.to

theorem GeSub
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c ≥ a + b) :
-- imply
  c - b ≥ a :=
-- proof
  LeAdd.to.Le_Sub h


end Algebra.Ge_Add.to

-- created on 2024-11-27
