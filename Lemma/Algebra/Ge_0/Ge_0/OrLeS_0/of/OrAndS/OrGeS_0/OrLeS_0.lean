import Lemma.Algebra.Lt.of.Le.Lt
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α}
-- given
  (h₀ : x ≤ 0 ∨ y ≤ 0)
  (h₁ : (x ≥ 0 ∨ y ≥ 0))
  (h₂ : x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0) :
-- imply
  x ≥ 0 ∧ y ≥ 0 ∧ (x ≤ 0 ∨ y ≤ 0) := by
-- proof
  cases' h₂ with h₂ h₂
  ·
    let ⟨_, _⟩ := h₂
    constructor
    ·
      assumption
    ·
      constructor <;> assumption
  ·
    constructor <;>
    ·
      exfalso
      let ⟨h₂_left, h₂_right⟩ := h₂
      simp_all
      cases' h₀ with h₀ h₀ <;>
      ·
        cases' h₁ with h₁ h₁
        ·
          have := Lt.of.Le.Lt h₁ h₂_left
          simp at this
        ·
          have := Lt.of.Le.Lt h₁ h₂_right
          simp at this


-- created on 2025-04-18
-- updated on 2025-04-19
