import Axiom.Basic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β}
-- given
  (h : (p → R x a) ∧ (¬p → R x b)) :
-- imply
  R x (if p then
    a
  else
    b) := by
-- proof
  by_cases hp : p <;>
  ·
    simp [hp] at *
    exact h


-- created on 2025-01-12
-- updated on 2025-04-11
