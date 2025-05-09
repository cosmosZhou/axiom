import sympy.sets.sets
import Axiom.Set.Mem_Range.of.Lt
open Set


@[main]
private lemma main
  {x y : ℕ → α}
-- given
  (h₀ : m < n)
  (h₁ : ∀ i ∈ range n, x i = y i) :
-- imply
  x m = y m := by
-- proof
  -- Apply the universal statement `h₁` to the specific index `m`
  apply h₁ m
  -- Provide the proof that `m < n` (from `h₀`) to satisfy the membership in `range n`
  apply Mem_Range.of.Lt h₀


-- created on 2025-04-26
