import Axiom.sympy.core.containers.vector
import Axiom.Algebra.Eq_.Sum.Zero
import Axiom.Algebra.Eq_.Dot.Zero
import Axiom.Algebra.Map.eq.Cons_MapTail
import Axiom.Algebra.SumCons.eq.Add_Sum.vector
import Axiom.Algebra.DotConsS.eq.AddDotS
open Mathlib

namespace Algebra.All_Eq_.SumMap_FunMul

theorem DotMapS
  -- [AddMonoid β]
  [Add β] [Zero β] [Mul β]
  {f₁ f₂ : α → β} :
-- imply
  ∀ {s : Vector α n}, (s.map fun x => f₁ x * f₂ x).sum = s.map f₁ ⬝ s.map f₂ := by
-- proof
  induction n with
  | zero =>
    -- Base case: n = 0
    -- Eq_.Dot.Zero
    -- Eq_.Sum.Zero
    simp
  | succ n ih =>
    -- Inductive case: n = n + 1
    intro s
    rw [
      Map.eq.Cons_MapTail,
      SumCons.eq.Add_Sum.vector,
      Map.eq.Cons_MapTail,
      Map.eq.Cons_MapTail,
      DotConsS.eq.AddDotS,
      ih
    ]

end Algebra.All_Eq_.SumMap_FunMul

-- created on 2024-07-01
