import Mathlib.Tactic

namespace algebra.all.then.all


theorem fn
  {s : List α}
  {f₁ f₂ : α → β}
  {f₃ : β → γ}
-- given
  (h : ∀ x ∈ s, f₁ x = f₂ x) :
-- imply
  ∀ x ∈ s, f₃ (f₁ x) = f₃ (f₂ x) := by
-- proof
  intros x x_in_s
  rw [h x x_in_s]

end algebra.all.then.all
open algebra.all.then.all
