import Axiom.Basic

namespace Algebra.All_Eq.to


theorem All_EqFunS
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

end Algebra.All_Eq.to

-- created on 2024-07-01
