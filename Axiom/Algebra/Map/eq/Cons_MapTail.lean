import Axiom.sympy.core.containers.vector
open Mathlib

namespace Algebra.Map.eq

theorem Cons_MapTail
  {s : Vector α (Nat.succ n)}
  {f : α → β} :
-- imply
  s.map f = f s.head ::ᵥ s.tail.map f := by
-- proof
  have h : s = s.head ::ᵥ s.tail := by simp
  -- rewrite only the left-hand side
  rw [h]
  apply Vector.map_cons

end Algebra.Map.eq

-- created on 2024-07-01
