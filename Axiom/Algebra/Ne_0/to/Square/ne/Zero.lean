import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Square.eq.Mul
import Axiom.Algebra.Mul.eq.Zero.to.OrEqS_0
namespace Algebra.Ne_0.to.Square.ne

theorem Zero
  [LinearOrderedRing α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a² ≠ 0 := by
-- proof
  by_contra h'
  rw [Square.eq.Mul] at h'
  have h := Mul.eq.Zero.to.OrEqS_0 h'
  simp at h
  contradiction


end Algebra.Ne_0.to.Square.ne

-- created on 2024-11-29
