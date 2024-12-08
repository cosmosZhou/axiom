import Axiom.Basic

namespace Algebra.MapMap.eq

theorem Map_Comp
  (g : β → γ)
  (f : α → β)
  (l : List α) :
-- imply
  (l.map f).map g = l.map (g ∘ f) := by
-- proof
  simp [List.map_map]


end Algebra.MapMap.eq

-- created on 2024-07-01
