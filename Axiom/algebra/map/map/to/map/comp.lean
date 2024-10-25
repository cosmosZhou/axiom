import Mathlib.Tactic

set_option linter.dupNamespace false

namespace algebra.map.map.to.map

theorem comp
  (g : β → γ)
  (f : α → β)
  (l : List α) :
-- imply
  (l.map f).map g = l.map (g ∘ f) := by
  simp [List.map_map]


end algebra.map.map.to.map
open algebra.map.map.to.map
