import Axiom.Basic


@[main]
private lemma main
-- given
  (h : p ∧ q ∨ r) :
-- imply
  (p ∨ r) ∧ (q ∨ r) := by
-- proof
  cases h with
  | inl hpq =>
    have hp : p := hpq.left
    have hq : q := hpq.right
    exact ⟨Or.inl hp, Or.inl hq⟩
  | inr hr =>
    exact ⟨Or.inr hr, Or.inr hr⟩


-- created on 2024-07-01
