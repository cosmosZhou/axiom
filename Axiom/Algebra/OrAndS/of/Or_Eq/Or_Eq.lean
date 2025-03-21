import Axiom.Basic


@[main]
private lemma main
  {x a b : α}
-- given
  (h0 : ¬p ∨ x = a)
  (h1 : p ∨ x = b) :
-- imply
  x = a ∧ p ∨ x = b ∧ ¬p := by
-- proof
  by_cases hp : p <;>
  ·
    simp [hp] at *
    assumption


-- created on 2025-01-12
