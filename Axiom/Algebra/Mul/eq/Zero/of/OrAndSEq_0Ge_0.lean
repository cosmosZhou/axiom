import Axiom.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α}
-- given
  (h : x = 0 ∧ y ≥ 0 ∨ y = 0 ∧ x ≥ 0) :
-- imply
  x * y = 0 := by
-- proof
  cases' h with h h <;>
  ·
    let ⟨h, _⟩ := h
    rw [h]
    simp


-- created on 2025-04-19
