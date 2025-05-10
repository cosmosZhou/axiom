import sympy.sets.sets
import Lemma.Logic.All_Not.of.NotAny
import Lemma.Logic.All.of.All.All_Imp
import Lemma.Logic.All_And.of.All.All
import Lemma.Logic.NotAny_Not.of.All
open Logic


@[main]
private lemma main
  {n : ℕ}
  {a : ℝ}
  {x : ℕ → ℝ}
-- given
  (h₀ : ∀ i ∈ range n, x i ≥ a)
  (h₁ : ∃ i ∈ range n, x i ≠ a) :
-- imply
  ∃ i ∈ range n, x i > a := by
-- proof
  by_contra h
  have h := All_Not.of.NotAny.finset h
  have : ∀ t : ℝ, ¬t > a → t ≤ a := by
    intro t h
    linarith
  have h_Ge_0 := All.of.All.All_Imp.finset (α := ℝ) this h
  have h := All_And.of.All.All.finset h₀ h_Ge_0
  have : ∀ t : ℝ, t ≥ a ∧ t ≤ a → t = a := by
    intro t h
    linarith
  have h := All.of.All.All_Imp.finset this h
  have := NotAny_Not.of.All h
  have h_NotAny : ¬∃ i ∈ range n, x i ≠ a := by
    simp [this]
    simp at h
    exact h
  contradiction


-- created on 2025-04-06
-- updated on 2025-04-26
