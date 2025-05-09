import Axiom.Logic.Or_Not.law_of_excluded_middle
open Logic


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∨ q ∧ ¬p ↔ p ∨ q := by
-- proof
  apply Iff.intro <;>
    intro h
  ·
    -- Forward direction: Assume p ∨ (q ∧ ¬p), prove p ∨ q
    cases' h with h h
    exact Or.inl h
    exact Or.inr h.left
  ·
    -- Backward direction: Assume p ∨ q, prove p ∨ (q ∧ ¬p)
    cases' h with h h
    exact Or.inl h
    simp [h]
    apply Or_Not.law_of_excluded_middle


-- created on 2025-04-18
