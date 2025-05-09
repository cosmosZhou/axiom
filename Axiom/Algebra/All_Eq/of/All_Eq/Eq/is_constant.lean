import sympy.sets.sets
import Axiom.Algebra.All_Eq.of.All_Eq.Eq
open Algebra


@[main]
private lemma main
  {x : ℕ → α}
  {a : α}
-- given
  (h₀ : x n = a)
  (h₁ : ∀ i ∈ range n, x i = a) :
-- imply
  ∀ i ∈ range (n + 1), x i = a := by
-- proof
  let y := fun _ : ℕ => a
  have := All_Eq.of.All_Eq.Eq (y := y) h₀ h₁
  simp only [y] at this
  assumption


-- created on 2025-04-26
