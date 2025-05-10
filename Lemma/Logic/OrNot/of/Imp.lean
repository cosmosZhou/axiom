import Lemma.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → q) :
-- imply
  ¬p ∨ q := by
-- proof
  by_cases hp : p
  -- Case 1: p is true
  exact Or.inr (h hp)
  -- Case 2: p is false
  exact Or.inl hp


-- created on 2024-07-01
