import sympy.sets.sets
import Lemma.Algebra.Root_Add_2.le.Sqrt.of.Ge_1
import Lemma.Logic.All.of.All.All_Imp
open Algebra Logic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : ∀ i ∈ range n, x i ≥ 1) :
-- imply
  ∀ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) ≤ √(x i) := by
-- proof
  have : ∀ (t : ℝ) (i : ℕ), t ≥ 1 → (t ^ (1 / (i + 2) : ℝ) ≤ √t) := by
    intro t i h
    apply Root_Add_2.le.Sqrt.of.Ge_1 h
  exact All.of.All.All_Imp.binary this h₀


-- created on 2025-04-06
