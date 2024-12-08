import Axiom.Algebra.Gt.to.Ge_Add_1
import Axiom.Algebra.Ge.to.GeSubS
import Axiom.Algebra.SubAdd.eq.Add_Sub

namespace Algebra.Gt.to

theorem GeSub_1
  {x y : ℤ}
-- given
  (h : x > y) :
-- imply
  x - 1 ≥ y := by
-- proof
  have h' := Gt.to.Ge_Add_1 h

  have h' := Ge.to.GeSubS h' 1

  rw [SubAdd.eq.Add_Sub] at h'
  simp at h'

  exact h'


end Algebra.Gt.to

-- created on 2024-07-01
