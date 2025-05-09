import Axiom.Basic


@[main]
private lemma nat
  {x y a b : ℕ}
-- given
  (h : x = a ∨ y = b) :
-- imply
  (x - a) * (y - b) = (0 : ℤ) := by
-- proof
  -- Split the hypothesis into two cases: x = a or y = b
  cases h with
  | inl h₀ =>
    -- Case 1: x = a
    -- Substitute x = a into the expression and simplify
    subst h₀
    simp
  | inr h₁ =>
    -- Case 2: y = b
    -- Substitute y = b into the expression and simplify
    subst h₁
    simp


@[main]
private lemma main
  [Ring α]
  {x y a b : α}
-- given
  (h : x = a ∨ y = b) :
-- imply
  (x - a) * (y - b) = 0 := by
-- proof
  -- Split the hypothesis into two cases: x = a or y = b
  cases h with
  | inl h₀ =>
    -- Case 1: x = a
    -- Substitute x = a into the expression and simplify
    subst h₀
    simp
  | inr h₁ =>
    -- Case 2: y = b
    -- Substitute y = b into the expression and simplify
    subst h₁
    simp


-- created on 2025-04-11
