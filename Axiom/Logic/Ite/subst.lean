import sympy.core.relational
import Axiom.Basic


@[main]
private lemma main
  [Decidable p]
  {x : α}
  {f : α → β}
  {y : β} :
-- imply
  (if x = a ∧ p then
    f x
  else
    y) = if x = a ∧ p then
    f a
  else
    y := by
-- proof
  denote h_P : P = left
  rw [← h_P]


-- created on 2025-04-09
