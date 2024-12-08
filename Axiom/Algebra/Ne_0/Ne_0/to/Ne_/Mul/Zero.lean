import Axiom.Basic

namespace Algebra.Ne_0.Ne_0.to.Ne_.Mul

theorem Zero
  [Field α]
  {a b : α}
-- given
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
-- imply
   a * b ≠ 0 := by
-- proof
  simp [h0, h1]


end Algebra.Ne_0.Ne_0.to.Ne_.Mul

-- created on 2024-07-01
