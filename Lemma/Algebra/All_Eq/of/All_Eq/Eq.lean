import sympy.sets.sets
import Lemma.Set.Mem_Range.ou.Eq.of.Mem_Range
open Set


@[main]
private lemma main
  {x y : ℕ → α}
-- given
  (h₀ : x n = y n)
  (h₁ : ∀ i ∈ range n, x i = y i) :
-- imply
  ∀ i ∈ range (n + 1), x i = y i := by
-- proof
  -- Introduce the index `i` and the hypothesis `hi` that `i` is in the range `n + 1`.
  intro i hi
  -- Perform case analysis on the hypothesis `hi` to split into two cases: `i < n` and `i = n`.
  cases' Mem_Range.ou.Eq.of.Mem_Range hi with h h
  ·
    -- Case 1: `i < n`. Use the hypothesis `h₁` which states `x i = y i` for all `i` in the range `n`.
    simp_all [h₁]
  ·
    -- Case 2: `i = n`. Use the hypothesis `h₀` which states `x n = y n`.
    simp_all [h₀]


-- created on 2025-04-26
