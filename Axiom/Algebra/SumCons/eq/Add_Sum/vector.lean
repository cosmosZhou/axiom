import Axiom.sympy.core.containers.vector
import Axiom.Algebra.SumCons.eq.Add_Sum
open Mathlib

namespace Algebra.SumCons.eq.Add_Sum

theorem vector
  -- [AddMonoid α]
  [Add α] [Zero α]
  {l : Vector α n}
  {a : α} :
-- imply
  (a ::ᵥ l).sum = a + l.sum :=
-- proof
  SumCons.eq.Add_Sum


end Algebra.SumCons.eq.Add_Sum

-- created on 2024-07-01
