import Axiom.Algebra.Ge.to.GeSubS
import Axiom.Algebra.Sub.eq.Zero
import Axiom.Algebra.Sub0.eq.Neg
namespace Algebra.Ge_0.to.Neg.le

theorem Zero
  [OrderedAddCommGroup α]
  {a : α}
-- given
  (h : a ≥ 0) :
-- imply
  -a ≤ 0 := by
-- proof
  have h := Ge.to.GeSubS h a
  simp only [Sub.eq.Zero, Sub0.eq.Neg] at h
  exact h


end Algebra.Ge_0.to.Neg.le

-- created on 2024-11-29
