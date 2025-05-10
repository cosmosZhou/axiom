import sympy.sets.sets
import Lemma.Algebra.All_Eq.of.All_Eq.Lt
open Algebra


@[main]
private lemma main
  {x : ℕ → α}
  {a : α}
-- given
  (h₀ : m<n)
  (h₁ : ∀ i ∈ range n, x i = a) :
-- imply
  ∀ i ∈ range m, x i = a := by
-- proof
  let y := fun _ : ℕ => a
  have := All_Eq.of.All_Eq.Lt (y := y) h₀ h₁
  simp only [y] at this
  assumption


-- created on 2025-04-26
