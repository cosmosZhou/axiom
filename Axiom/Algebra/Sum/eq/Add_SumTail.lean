import Axiom.sympy.core.containers.vector
import Axiom.Algebra.SumCons.eq.Add_Sum.vector
import Axiom.Algebra.Eq_.Sum.Zero
import Axiom.Algebra.HeadD.simp
import Axiom.Algebra.HeadDCons.simp

open Mathlib
namespace Algebra.Sum.eq

theorem Add_SumTail
  [AddMonoid α]
  -- [Add α] [Zero α]
  {l : Vector α n} :
-- imply
  l.sum = (l.headD 0) + l.tail.sum := by
-- proof
  cases n with
  | zero =>
    -- HeadD.simp
    --- Eq_.Sum.Zero
    simp

  | succ n =>
    have h : l = l.head ::ᵥ l.tail := by simp
    rw [h]

    rw [
      SumCons.eq.Add_Sum.vector,
      HeadDCons.simp
    ]
    simp

end Algebra.Sum.eq

-- created on 2024-07-01
